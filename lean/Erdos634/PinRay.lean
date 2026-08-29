import Mathlib.Tactic

/-!
# The pin ray never exits at an integer distance

Erdős #634, `e = 1`.  At the pin `J` of an `a|c|b` configuration the `c`-tile presents `β`, so its
`a`-edge from `J` runs parallel to the target's left side, whose base angle is also `β`.  The
overrunning edges beyond the forced `α`-tile are **collinear with that `a`-edge**, so the whole
displacement marches along one fixed ray, monotonically, in steps of `f-1` or `a`.

That ray leaves the target through the right side at distance

  `T = f³ (N₀ - p f) / N₀`,   `N₀ = 3f² - 1`,   the pin at `J = p f`,

and `T` is never an integer: `gcd(f, N₀) = 1`, so `N₀ ∣ f³(N₀ - pf)` forces `N₀ ∣ p`, while
`1 ≤ p ≤ f-1 < N₀`.  Verified for all `4 ≤ f < 40` and every `p`, without exception.

**What this buys.**  Tile edges have integer lengths `f`, `f²-1`, `f²`.  If the chain of edges
along the ray ever reaches the boundary, both of its ends are anchored — `J` on the base, the exit
on the perimeter — so its length would be a sum of tile edges, hence an integer.  It is not.  *The
configuration therefore dies outright the moment the chain reaches the boundary.*

**What it does not buy.**  Nothing forces the chain to continue: past an edge's far endpoint the
ray may pass through a tile's interior rather than along another edge.  That single implication —
that the chain, once started at the pin, propagates to the boundary — is now the entire remaining
obstacle for the `a|c|b` words.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.PinRay

/-- `f` and `N₀ = 3f² - 1` are coprime: `3f·f - (3f² - 1) = 1`. -/
theorem coprime_f_N0 (f : ℤ) : IsCoprime f (3 * f ^ 2 - 1) :=
  ⟨3 * f, -1, by ring⟩

/-- **The exit distance is not an integer.**  `N₀ T = f³ (N₀ - p f)` is unsolvable in integers when
`1 ≤ p < N₀` and `f` is coprime to `N₀`. -/
theorem exit_not_integral (f p N₀ T : ℤ) (hco : IsCoprime N₀ f)
    (hp1 : 1 ≤ p) (hp2 : p < N₀) (h : N₀ * T = f ^ 3 * (N₀ - p * f)) : False := by
  have hd : N₀ ∣ p * f ^ 4 := by
    have hsplit : f ^ 3 * N₀ - f ^ 3 * (N₀ - p * f) = p * f ^ 4 := by ring
    have h1 : N₀ ∣ f ^ 3 * N₀ := ⟨f ^ 3, by ring⟩
    have h2 : N₀ ∣ f ^ 3 * (N₀ - p * f) := ⟨T, h.symm⟩
    have := dvd_sub h1 h2
    rwa [hsplit] at this
  have hcop4 : IsCoprime N₀ (f ^ 4) := hco.pow_right
  have hpd : N₀ ∣ p := hcop4.dvd_of_dvd_mul_right hd
  have : N₀ ≤ p := Int.le_of_dvd (by omega) hpd
  omega

/-- The instance the geometry supplies: the pin sits at `p f` with `1 ≤ p ≤ f - 1`, well inside
`N₀ = 3f² - 1`, so the hypotheses of `exit_not_integral` hold at every member. -/
theorem pin_index_small (f p : ℤ) (hf : 2 ≤ f) (hp1 : 1 ≤ p) (hp2 : p ≤ f - 1) :
    p < 3 * f ^ 2 - 1 := by nlinarith

end Erdos634.PinRay
