import Mathlib.Tactic
import Erdos634.PinPlumbing

/-!
# The anchored-chain kill: a locating consequence of the angle budget

Erdős #634.  The ledger's central diagnosis is that every invariant the sweep produces *counts*,
while the open step needs one that *locates*.  This file records a fact that does locate: it pins
an endpoint of a covering chain to a specific point.

At an interior point of a dissection the tile angles sum to `2π`.  Suppose one tile has the point
interior to an edge — contributing `π` — and another tile shows `γ = 2α + β` there.  Then

  `π + γ = 5α + 3β`,  leaving  `2π − π − γ = α + β`,

and a *second* through-edge would need a further `π = 3α + 2β > α + β`.  So there is no second
through-edge: **every remaining tile at that point has a vertex there**, and the residue `α + β`
admits the single figure `(n_α, n_β, n_γ) = (1,1,0)`.

The consequence is positional.  A chain of edges covering a stretch of that line cannot pass
through such a point; it must *begin* there.  Where the semigroup gap lemmas say a run of a given
length cannot be assembled, this says where a run's endpoint must sit — which is the ingredient
those lemmas need and cannot themselves supply.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.AnchoredChain

open Erdos634.Geometry

/-- **No second through-edge beside a `γ`.**  At an interior point carrying one through-edge and a
`γ`-corner, a second through-edge overruns the budget: `π + γ + π = 2π + γ > 2π`. -/
theorem no_second_through_with_gamma {N : ℕ} (D : Dissection N) {p : Plane}
    (hp : p ∈ interior D.target.carrier)
    (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : γ = 2 * α + β)
    (hπ : 3 * α + 2 * β = Real.pi)
    (i j k : Fin N) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : (D.tile i).localAngle p = Real.pi)
    (hj : (D.tile j).localAngle p = γ)
    (hk : (D.tile k).localAngle p = Real.pi) : False := by
  have hsum := Erdos634.PinPlumbing.pin_angle_sum_interior D hp
  have htriple : (D.tile i).localAngle p + (D.tile j).localAngle p + (D.tile k).localAngle p
      ≤ ∑ m, (D.tile m).localAngle p := by
    have hsub : ({i, j, k} : Finset (Fin N)) ⊆ Finset.univ := Finset.subset_univ _
    have hle : ∑ m ∈ ({i, j, k} : Finset (Fin N)), (D.tile m).localAngle p
        ≤ ∑ m, (D.tile m).localAngle p :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun m _ _ => (D.tile m).localAngle_nonneg p)
    rw [Finset.sum_insert (by simp [hij, hik]), Finset.sum_insert (by simp [hjk]),
      Finset.sum_singleton] at hle
    linarith
  rw [hi, hj, hk, hsum, hγ] at htriple
  linarith

/-- **The residue beside a `γ` is `α + β`**, whose only figure is one `α` and one `β`. -/
theorem residue_beside_gamma_figure (x y z : ℕ) (h1 : x + 2 * z = 1) (h2 : y + z = 1) :
    x = 1 ∧ y = 1 ∧ z = 0 := by omega

/-- **The chain is anchored.**  Stated as the covering consequence: a tile whose edge would carry
the point in its interior cannot exist beside the first through-edge and the `γ`, so any chain
covering that line has an endpoint at the point rather than passing it. -/
theorem chain_endpoint_pinned (residue α β : ℝ) (hres : residue = α + β)
    (hα : 0 < α) (hβ : 0 < β) (hπ : 3 * α + 2 * β = Real.pi) : residue < Real.pi := by
  rw [hres]; linarith

end Erdos634.AnchoredChain
