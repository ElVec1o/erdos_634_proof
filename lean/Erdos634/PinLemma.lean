import Mathlib.Tactic
import Erdos634.Dissection
import Erdos634.FanStep

/-!
# The pin lemma: a `γ|α` base junction holds exactly one further tile, and it presents `β`

Erdős #634, `e = 1` hole.  The fan phenomenon of `FanKill`/`FanStep` — mined from the engine and
verified at eleven data points — turns out to be the *search's* view of a fact whose proof is
direct.  `Dissection.sum_localAngle_eq` (the discharged `G2`) gives, at **every** point of the
target, `∑ i, localAngle (tile i) p = localAngle target p`; at a point interior to the base edge
the right side is `π`.  So in a completed tiling the angles at a base junction sum to `π`
**exactly**, and the wedge between a `γ`-flank and an `α`-flank carries a tile-angle multiset
summing to exactly `β = π - γ - α`.  By the irrationality-driven multiplicity system the only such
multiset is a single `β` (`pin_forces_single_beta`); a tile holding the junction in the interior of
one of its edges is excluded outright, since it alone contributes `π` and the flanks are positive
(`no_through_tile`).

The engine's fans are what the impossible looks like to a solver: partial states that advance by
`α` and can never close.  The fan law (`⌊β/α⌋`) measures the depth of that impossibility; the pin
lemma removes the need for any induction over it.

What consumes this: at the `(4,2)`-type junction the forced `β`-tile has flanks `a` and `c` on
rays of length `b`, dying on the two-gap contract (`b - a` and `c - b = 1`).  The remaining
instantiation is `wall_partition` along those rays; the junction's flank angles (`γ` west from the
forced corner figure, `α` east from the `c`-tile's orientation) are the `e1reduce`-level corner
theory.  The mirrored `c`-tile case (`β` east flank) forces a single `α`-tile instead
(`pin_forces_single_alpha`), which is the head of the engine's second cascade.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.PinLemma

/-- **A through-tile is impossible at a flanked junction.**  If some tile holds the junction in the
interior of one of its edges it contributes `π` by itself; with the two positive flank angles the
sum exceeds `π`. -/
theorem no_through_tile (flankW flankE rest : ℝ) (hW : 0 < flankW) (hE : 0 < flankE)
    (hrest : 0 ≤ rest) (hsum : flankW + flankE + (Real.pi + rest) = Real.pi) : False := by
  linarith

/-- **The wedge multiset is forced: exactly one `β`.**  Tiles with a vertex at the junction inside
the wedge contribute `x` copies of `α`, `y` of `β`, `z` of `γ = 2α + β`; the angle sum at the
junction gives `x·α + y·β + z·γ = β`, and independence of `α, β` over `ℚ` (from `α/π` irrational)
forces `(x, y, z) = (0, 1, 0)`. -/
theorem pin_forces_single_beta {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (x y z : ℕ)
    (hsum : (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * (2 * α + β) = β) :
    x = 0 ∧ y = 1 ∧ z = 0 := by
  have h := Erdos634.Geometry.vertex_multiplicities hrel hirr x y z 0 1 (by push_cast; linarith)
  omega

/-- **The mirrored case: exactly one `α`.**  If the `c`-tile shows `β` at the junction the wedge is
`π - γ - β = α`, and the forced multiset is a single `α`. -/
theorem pin_forces_single_alpha {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (x y z : ℕ)
    (hsum : (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * (2 * α + β) = α) :
    x = 1 ∧ y = 0 ∧ z = 0 := by
  have h := Erdos634.Geometry.vertex_multiplicities hrel hirr x y z 1 0 (by push_cast; linarith)
  omega

/-- **The forced `β`-tile dies.**  Its flanks are `a` and `c`, laid along rays of length
`b = f² - 1`: the `a` leaves the run `b - a = f² - 1 - f`, the `c` leaves the stub `c - b = 1`,
and both are semigroup gaps (`FanKill.two_gap_contract`).  Stated on the covering data the
`wall_partition` instantiation supplies. -/
theorem beta_tile_dies (f x y z : ℕ) (hf : 3 ≤ f)
    (hcover : x * f + y * (f * f - 1) + z * (f * f) = f * f - 1 - f ∨
              x * f + y * (f ^ 2 - 1) + z * f ^ 2 = 1) : False := by
  rcases hcover with h | h
  · exact (Erdos634.FanKill.two_gap_contract f x y z hf).1 h
  · exact (Erdos634.FanKill.two_gap_contract f x y z hf).2 h

end Erdos634.PinLemma
