import Erdos634.ThickJunctionCoords
import Erdos634.BaseBetaE1

/-!
# `modelAlpha 2 3` is an irrational multiple of `π`

Erdős #634, base-`β` branch, room `e2b` (the crux at `(e,f) = (2,3)`, `N = 23`).

`BaseBetaE1.tile_alpha_irrational` (`BaseBetaE1.lean`) is already **`(e,f)`-general**: for any
`1 ≤ e < f` it derives `α ∉ ℚπ` from `sin(α/2) = e/(2f)` via Niven's theorem, with no appeal to
`e = 1`.  Nothing in the corpus instantiates it away from `e = 1`: `MarchKillsFan.modelAlpha_pos`,
`.modelAlpha_lt_pi_div_three`, `.sin_half_modelAlpha`, `.modelAlpha_irrational` are all stated only
for `modelAlpha 1 f`.  This file supplies the `(2,3)` instance directly, by the identical route
(half-angle from `cos_modelAlpha`, sign from `angles_pos_63`/`modelBeta_mem`), needed to discharge
the `hirr` hypothesis of the *general* vertex-figure trichotomy
`TileAt.congruentDissection_boundary_figure_cases` at this instance — a hypothesis
`ThickJunctionCoords.lean` did not need (it used the narrower `JunctionWedge.junction_step`, which
carries no irrationality hypothesis) but which the six *mixed* junctions of the crux word do need,
since their local figure is not assumed but derived from the general boundary-point classification.

**What is proved.**  `sin_half_modelAlpha_23 : sin(modelAlpha 2 3 / 2) = 1/3` (the `(e,f)=(2,3)`
half-angle identity, by the same computation as `MarchKillsFan.sin_half_modelAlpha` at `e=1` but
from `cos_modelAlpha 2 3 = 7/9` instead of `cos_modelAlpha 1 f`), and
`modelAlpha_irrational_23 : ¬ ∃ r : ℚ, modelAlpha 2 3 = r * π`, by `tile_alpha_irrational 2 3`.

**Scope.**  The two-line generalisation to arbitrary `(e,f)` (replace `2,3` by `e,f` and
`angles_pos_63`/`cos_modelAlpha 2 3` by their general forms, which already exist) is visible but not
taken here, per this room's minimal-generality budget (Rule I11): only the `(2,3)` instance is
needed for this crux, and only that instance is proved.

Axiom-clean beyond the standard three; no `sorry`.
-/

namespace Erdos634.ThickAngleIrrational

open Erdos634.BaseBetaTargetCoord Erdos634.ThickJunctionCoords

/-- **The half-angle identity at `(e,f) = (2,3)`**: `sin(α/2) = e/(2f) = 1/3`, from
`cos_modelAlpha 2 3 = 7/9` via `sin² = (1 − cos)/2`, matching `MarchKillsFan.sin_half_modelAlpha`'s
method at `e = 1` exactly, redone here from the general `cos_modelAlpha` rather than the `e=1`
specialisation. -/
theorem sin_half_modelAlpha_23 : Real.sin (modelAlpha 2 3 / 2) = 1 / 3 := by
  have hα0 : 0 < modelAlpha 2 3 := angles_pos_63.1
  have hβ := modelBeta_mem (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) < 3)
  have hαπ : modelAlpha 2 3 < Real.pi := by
    simp only [modelAlpha]; have := Real.pi_pos; nlinarith [hβ.1]
  have hsq : Real.sin (modelAlpha 2 3 / 2) ^ 2 = (1 / 3 : ℝ) ^ 2 := by
    rw [Real.sin_sq_eq_half_sub, show 2 * (modelAlpha 2 3 / 2) = modelAlpha 2 3 by ring,
      cos_modelAlpha (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) < 3)]
    norm_num
  have hnn : 0 ≤ Real.sin (modelAlpha 2 3 / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  exact (sq_eq_sq₀ hnn (by norm_num)).mp hsq

/-- **`modelAlpha 2 3` is an irrational multiple of `π`.**  `BaseBetaE1.tile_alpha_irrational`
(already general in `(e,f)`) at `e = 2, f = 3`, fed by `sin_half_modelAlpha_23`.  This is the new
content: the first instance of `tile_alpha_irrational` ever taken away from `e = 1` in this corpus. -/
theorem modelAlpha_irrational_23 : ¬ ∃ r : ℚ, modelAlpha 2 3 = (r : ℝ) * Real.pi := by
  refine Erdos634.BaseBetaE1.tile_alpha_irrational 2 3 (by norm_num) (by norm_num) _ ?_
  rw [sin_half_modelAlpha_23]
  push_cast
  norm_num

/-- Non-vacuity is immediate: `modelAlpha 2 3` is a genuine positive real number
(`ThickJunctionCoords.angles_pos_63`), not a free variable, and the theorem above applies to it. -/
theorem modelAlpha_irrational_23_nonvacuous : 0 < modelAlpha 2 3 :=
  angles_pos_63.1

#print axioms sin_half_modelAlpha_23
#print axioms modelAlpha_irrational_23

end Erdos634.ThickAngleIrrational
