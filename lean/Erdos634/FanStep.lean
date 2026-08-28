import Mathlib.Tactic
import Erdos634.FanKill

/-!
# The fan step: the per-step case analysis of the `(4,2)` junction, closed arithmetically

Erdős #634, `e = 1` hole.  `FanKill` proved the termination arithmetic of the `α`-fan.  This file
closes the *step*: at each stage of the fan, the possible fills of the remaining wedge are
exhausted by four cases, and every case except "another `α`-tile" dies by arithmetic already in
the corpus.  Combined with `FanKill`, the `(4,2)` junction's refutation is reduced to the standard
interface facts alone (a straight tiling segment is covered by whole tile edges; the angles of the
tiles at a vertex inside a wedge sum to at most the wedge).

## The step, read off the traces

The fan state after `k` steps: remaining wedge `β - kα` at the pin `J`, east flank a tile edge of
length `b` or `c` from `J`.  A tile meeting `J` inside the wedge presents `α`, `β`, or `γ`, or
passes an edge through `J` (contributing `π`).  The cases:

* `γ` **never fits**: `γ = 2α + β > β ≥ β - kα`  (`gamma_never_fits`).
* an **edge through `J` never fits**: `π = 3α + 2β > β`  (`through_never_fits`).
* `β` **fits only at `k = 0`**: `β ≤ β - kα` forces `k = 0`  (`beta_only_at_start`); and at `k = 0`
  the `β`-tile's flanks are `a` and `c` laid along rays of length `b`, dying on the gap `b - a`
  (`east_cover_gap`, via `two_gap_contract`) or the overrun `c - b = 1` (`one_is_gap`).
* `α` **advances the fan**: the remainder drops by exactly `α`, and the tile lays `b` (stub `1`
  beyond it, a gap) or `c` (overrun `1`, a gap) along the flank — the two chiralities observed as
  the binary choices of the cascade  (`alpha_advances`, `stub_is_gap`).

Termination is `FanKill.fan_dies`.  What remains outside arithmetic: the interface facts named
above, which the corpus carries at `Dissection`/`WallChain` level, and the candidate-enumeration
completeness of the engine (certified computation).  No other geometric input is consumed.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.FanStep

/-- **`γ` never fits in the wedge**, at any stage: `γ = 2α + β > β ≥ β - kα`. -/
theorem gamma_never_fits (a b : ℝ) (ha : 0 < a) (k : ℕ) :
    b - (k : ℝ) * a < 2 * a + b := by
  have hk : (0 : ℝ) ≤ (k : ℝ) * a := by positivity
  linarith

/-- **An edge through the pin never fits**: it contributes `π = 3α + 2β > β ≥ β - kα`. -/
theorem through_never_fits (a b p : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hp : p = 3 * a + 2 * b) (k : ℕ) : b - (k : ℝ) * a < p := by
  have hk : (0 : ℝ) ≤ (k : ℝ) * a := by positivity
  rw [hp]; linarith

/-- **`β` fits only at the start**: `β ≤ β - kα` forces `k = 0`. -/
theorem beta_only_at_start (a b : ℝ) (ha : 0 < a) (k : ℕ)
    (h : b ≤ b - (k : ℝ) * a) : k = 0 := by
  by_contra hk
  have h1 : 1 ≤ (k : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
  nlinarith

/-- **The `α`-step advances by exactly `α`**: the remainder after `k+1` steps is the remainder
after `k` steps minus `α`. -/
theorem alpha_advances (a b : ℝ) (k : ℕ) :
    b - ((k : ℝ) + 1) * a = (b - (k : ℝ) * a) - a := by ring

/-- **Both chirality stubs are the same gap.**  Laying `b` along a `c`-flank leaves `c - b = 1`;
laying `c` along a `b`-flank overruns by `c - b = 1`.  One identity covers both, and `1` is below
every semigroup generator (`FanKill.one_is_gap`). -/
theorem stub_is_gap (f x y z : ℕ) (hf : 2 ≤ f)
    (h : x * f + y * (f ^ 2 - 1) + z * f ^ 2 = f ^ 2 - (f ^ 2 - 1)) : False := by
  have h1 : f ^ 2 - (f ^ 2 - 1) = 1 := by
    have h2 : 1 ≤ f ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  rw [h1] at h
  exact FanKill.one_is_gap f x y z hf h

/-- **The four-case exhaustion, assembled.**  In the remaining wedge after `k ≥ 1` steps, a tile at
the pin presenting angle `θ ∈ {α, β, γ}` either has `θ = α`, or does not fit; and an edge through
the pin does not fit.  (The `k = 0` `β`-case dies separately on the gaps.) -/
theorem step_exhaustion (a b g p θ : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hg : g = 2 * a + b) (hp : p = 3 * a + 2 * b) (k : ℕ) (hk : 1 ≤ k)
    (hfit : θ ≤ b - (k : ℝ) * a)
    (hcase : θ = a ∨ θ = b ∨ θ = g ∨ θ = p) : θ = a := by
  rcases hcase with h | h | h | h
  · exact h
  · exfalso
    have := beta_only_at_start a b ha k (h ▸ hfit)
    omega
  · exfalso
    have := gamma_never_fits a b ha k
    rw [h, hg] at hfit
    linarith
  · exfalso
    have := through_never_fits a b p ha hb hp k
    rw [h] at hfit
    linarith

end Erdos634.FanStep
