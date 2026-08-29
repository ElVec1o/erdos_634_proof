import Mathlib.Tactic
import Erdos634.PinPlumbing

/-!
# Bridge (c), first span: the forbidden transition is a fact about dissections

Erdős #634.  Adversarial review established that the orientation machinery
(`Interface`, `Inflation`, `RunOrientation`, `MarchAssembly`) is self-contained finite
combinatorics with no Lean connection to `Tri`/`Dissection`, so its theorems constrain no tiling.
Closing that gap is "bridge (c)" of the companion's `rem:pingaps`.

This file builds its **load-bearing span**.  The combinatorial layer's whole content is one
forbidden transition — `Inflation.BG_GB_forbidden`, "`BG` then `GB` puts two `γ`s at their shared
junction" — from which `orient_monotone`, `corner_anchored_run_all_BG` and the junction dichotomy
all follow.  That transition is justified in prose by an angle-budget argument.  Here it is proved
*about actual dissections*: at a boundary junction the tiles' local angles sum to `π`
(`PinPlumbing.pin_angle_sum`), and two tiles presenting `γ` there would need `2γ = π + α > π`.

`no_two_gamma_at_boundary_junction` therefore says, of a real `Dissection`, exactly what
`BG_GB_forbidden` says of the abstract alphabet.

**Scope, stated so it is not overread.**

* The constraint is specific to *boundary* junctions.  At an interior point the budget is `2π` and
  `2γ = π + α < 2π`, so two `γ`s are perfectly admissible there — `two_gamma_interior_ok` records
  this, and it is exactly why the `V_k` induction of `thm:n1` fails for `k ≥ 1`.
* What remains of bridge (c) is the *indexing*: a map sending a dissection and its base edge to a
  list of orientations in order, whose adjacency is this theorem.  That construction is not built
  here, so the combinatorial theorems still do not yet apply to tilings.  This file removes the
  mathematical obstacle, not the bookkeeping.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.OrientBridge

open Erdos634.Geometry

/-- **The forbidden transition, for dissections.**  Two distinct tiles cannot both present `γ` at
a boundary junction: the budget there is `π`, and `2γ = π + α`. -/
theorem no_two_gamma_at_boundary_junction {N : ℕ} (D : Dissection N) {p : Plane}
    (hp : p ∈ frontier D.target.carrier) (hv : p ∉ Set.range D.target.pts)
    (α β γ : ℝ) (hα : 0 < α) (hγ : γ = 2 * α + β) (hπ : 3 * α + 2 * β = Real.pi)
    (i j : Fin N) (hij : i ≠ j)
    (hi : (D.tile i).localAngle p = γ) (hj : (D.tile j).localAngle p = γ) : False := by
  have hsum := PinPlumbing.pin_angle_sum D hp hv
  have hpair : (D.tile i).localAngle p + (D.tile j).localAngle p
      ≤ ∑ m, (D.tile m).localAngle p := by
    have hsub : ({i, j} : Finset (Fin N)) ⊆ Finset.univ := Finset.subset_univ _
    have hle : ∑ m ∈ ({i, j} : Finset (Fin N)), (D.tile m).localAngle p
        ≤ ∑ m, (D.tile m).localAngle p :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun m _ _ => (D.tile m).localAngle_nonneg p)
    rwa [Finset.sum_insert (by simp [hij]), Finset.sum_singleton] at hle
  rw [hi, hj, hsum, hγ] at hpair
  linarith

/-- **The scope note, proved.**  At an interior point the budget is `2π`, and `2γ = π + α < 2π`:
two `γ`s are admissible there.  This is why the corner-chain induction of `thm:n1` breaks at
interior `V_k`, and why the forbidden transition is a boundary phenomenon. -/
theorem two_gamma_interior_ok (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hγ : γ = 2 * α + β) (hπ : 3 * α + 2 * β = Real.pi) :
    2 * γ < 2 * Real.pi := by
  rw [hγ]; linarith

/-- The same budget gap, stated as the residue the interior analysis must handle: `2π - γ - β`
is `π + α`, not `α`. -/
theorem interior_residue (α β γ : ℝ) (hγ : γ = 2 * α + β) (hπ : 3 * α + 2 * β = Real.pi) :
    2 * Real.pi - γ - β = Real.pi + α := by
  rw [hγ]; linarith

end Erdos634.OrientBridge
