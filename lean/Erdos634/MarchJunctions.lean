import Mathlib.Tactic
import Erdos634.PinLemma

/-!
# The march's junction catalogue: every fill the mirrored branch meets, forced

Erdős #634.  The uniform `(bp,2)` theorem's remaining hypothesis is that the mirrored branch
carries the march structure.  The march visits exactly two kinds of base junction — `a|a` along
the trailing run and `a|b` at the `b`-letter — and each junction's wedge is `π` minus the two
flank angles.  The `a`-edge's ends carry `β` or `γ`; the `b`-edge's ends carry `α` or `γ`.  This
file closes the whole case table:

| junction | flanks | wedge | forced fill | provider |
|---|---|---|---|---|
| `a\\|a` | `γ,β` or `β,γ` | `α` | one `α` (the partner) | `pin_forces_single_alpha` |
| `a\\|a` | `β,β` | `3α` | three `α`s | `three_alpha_fill` |
| `a\\|a` | `γ,γ` | — | **impossible**: `2γ > π` | `gamma_gamma_impossible` |
| `a\\|b` | `γ,α` | `β` | one `β` | `pin_forces_single_beta` |
| `a\\|b` | `β,γ` | `α` | one `α` | `pin_forces_single_alpha` |
| `a\\|b` | `β,α` | `γ` | `{γ}` or `{α,α,β}` | `gamma_wedge_fill` |
| `a\\|b` | `γ,γ` | — | impossible | `gamma_gamma_impossible` |

Every row is a proved multiplicity statement; the march hypothesis is thereby reduced to the
bookkeeping that composes these rows along the word with the run equations.  No junction type the
march can meet is missing from the table.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.MarchJunctions

/-- **Two `γ`-flanks never fit at a base junction**: `2γ = π + α > π`. -/
theorem gamma_gamma_impossible (a b g p : ℝ) (ha : 0 < a)
    (hg : g = 2*a + b) (hp : p = 3*a + 2*b) : p < 2 * g := by
  rw [hg, hp]; linarith

/-- **The `3α` wedge forces three `α`s**: `x + 2z = 3`, `y + z = 0` has the single solution
`(3,0,0)`. -/
theorem three_alpha_fill {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (x y z : ℕ)
    (hsum : (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * (2 * α + β) = 3 * α) :
    x = 3 ∧ y = 0 ∧ z = 0 := by
  have h := Erdos634.Geometry.vertex_multiplicities hrel hirr x y z 3 0 (by push_cast; linarith)
  omega

/-- **The `γ` wedge admits exactly `{γ}` or `{α,α,β}`**: `x + 2z = 2`, `y + z = 1`. -/
theorem gamma_wedge_fill {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (x y z : ℕ)
    (hsum : (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * (2 * α + β) = 2 * α + β) :
    (x = 0 ∧ y = 0 ∧ z = 1) ∨ (x = 2 ∧ y = 1 ∧ z = 0) := by
  have h := Erdos634.Geometry.vertex_multiplicities hrel hirr x y z 2 1 (by push_cast; linarith)
  omega

end Erdos634.MarchJunctions
