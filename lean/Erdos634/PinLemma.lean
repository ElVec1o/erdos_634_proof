import Mathlib.Tactic
import Erdos634.Dissection
import Erdos634.FanStep
import Erdos634.Interface

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

/-! ## The mirrored branch: a T-vertex ladder of forced `{α, β}` pairs

Read from the traces (f = 4): the mirrored `c`-tile shows `β` at the pin, forcing the single
`α`-tile (`pin_forces_single_alpha`), which lays its `b`-edge flush along the corner tile's
`b`-edge; the mirrored `c`-tile's apex then lands interior to the forced `α`-tile's `c`-edge — a
T-vertex.  There the angle budget is `2π`, the `γ`-apex and the through-edge (`π`) are already
present, and the remaining wedge is `2π - γ - π = π - γ = α + β`.  Its fill is forced to be
exactly one `α` and one `β` (`t_vertex_fill`) — the corpus's column-with-fillers structure, here
arising from the angle arithmetic alone.  The pair's two cyclic orders are the binary choices of
the engine's second cascade.  So the mirrored branch advances by forced `{α,β}` pairs along the
ladder of T-vertices; the induction's step is this lemma, and its termination is the base word —
which is where the per-word variation ((4,2) dying, (3,2) resisting) enters. -/

/-- **The T-vertex wedge is `α + β`.**  `2π - γ - π = π - γ = α + β` from the branch relations. -/
theorem t_vertex_wedge (a b g p : ℝ) (hg : g = 2*a + b) (hp : p = 3*a + 2*b) :
    2 * p - g - p = a + b := by rw [hg, hp]; ring

/-- **The T-vertex fill is forced: exactly one `α` and one `β`.**  A multiset of tile angles
summing to `α + β` has multiplicities solving `(x + 2z, y + z) = (1, 1)`, whose only solution is
`(1, 1, 0)`. -/
theorem t_vertex_fill {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (x y z : ℕ)
    (hsum : (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * (2 * α + β) = α + β) :
    x = 1 ∧ y = 1 ∧ z = 0 := by
  have h := Erdos634.Geometry.vertex_multiplicities hrel hirr x y z 1 1 (by push_cast; linarith)
  omega

/-- **The ladder's own coverage arithmetic**: the segment of the forced `α`-tile's `c`-edge beyond
the mirrored `c`-tile's `a`-edge has length `c - a = f² - f = f·(f-1)`, which IS in the semigroup
(`f - 1` copies of `a`) — so no gap kill fires there, and the ladder genuinely advances.  Recorded
because a silent assumption that it dies would be wrong. -/
theorem ladder_advances (f : ℤ) : f ^ 2 - f = (f - 1) * f := by ring

/-! ## The flank wiring: both pin hypotheses derived combinatorially

`Interface.flanks` records which sides flank which corner.  Two computations close the flank
identification:

* the corners flanking the `a`-side are exactly `{β, γ}` — so the corner tile, presenting `β` at
  the base corner with its `a` on the base (`corner_beta_unique` + the first letter of
  `thm:e1reduce`), presents `γ` at the pin  (`west_flank_gamma`);
* the corners flanking the `c`-side are exactly `{α, β}` — so the `c`-tile presents `α` or `β` at
  the pin, which is precisely the two-branch case split of the pin analysis
  (`east_flank_cases`). -/

open Erdos634.Interface in
/-- **The `a`-side's two ends carry `β` and `γ`**: if the near end is `β`, the far end is `γ`. -/
theorem west_flank_gamma (far : Corner)
    (hfar : (flanks far).1 = Edge.a ∨ (flanks far).2 = Edge.a)
    (hne : far ≠ Corner.beta) : far = Corner.gamma := by
  cases far <;> simp_all [flanks]

open Erdos634.Interface in
/-- **The `c`-side's two ends carry `α` and `β`**: the `c`-tile's pin corner is one of the two. -/
theorem east_flank_cases (c : Corner)
    (hc : (flanks c).1 = Edge.c ∨ (flanks c).2 = Edge.c) :
    c = Corner.alpha ∨ c = Corner.beta := by
  cases c <;> simp_all [flanks]

end Erdos634.PinLemma
