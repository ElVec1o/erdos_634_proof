import Erdos634.Congruence
import Erdos634.TilePlacement

/-!
# Every tile edge has one of the model's three lengths

Erdős #634. `thm:chain` and `prop:gammatrap` both need to classify a chain edge as an `a`-, `b`-
or `c`-edge (by length) before their inductive arguments can even be stated. This file is that
classifier's existence half: for a `CongruentDissection`, every edge of every tile has a length
equal to one of the model's three side lengths — `Tri.Congruent.dist_eq` already supplies the
matching permutation; this file names the consequence for a single edge.

The classifier does not by itself discharge `thm:chain` or `prop:gammatrap`: what remains is the
inductive propagation argument itself (an unbounded induction along a run, forcing the alternation
`α,γ,α,γ,...`), which is separate, substantial work not attempted here.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.Geometry

open Erdos634.TilePlacement

variable {N : ℕ}

private theorem third_index (x y : Fin 3) (hxy : x ≠ y) : ∃ j, j ≠ x ∧ j ≠ y := by
  revert x y hxy; decide

private theorem opp_eq_of_ne (x y j : Fin 3) (hxj : j ≠ x) (hyj : j ≠ y) (hxy : x ≠ y) :
    j + 1 = x ∧ j + 2 = y ∨ j + 1 = y ∧ j + 2 = x := by
  revert x y j hxj hyj hxy; decide

/-- **Every tile edge has one of the model's three lengths.** -/
theorem exists_matching_side (D : CongruentDissection N) (i : Fin N) (k : Fin 3) :
    ∃ j : Fin 3, dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) = sideOpp D.model j := by
  obtain ⟨σ, hσ⟩ := (D.tiles_congruent i).dist_eq
  have hne : σ k ≠ σ (k + 1) := by
    intro h
    have := σ.injective h
    have hk : ∀ x : Fin 3, x ≠ x + 1 := by decide
    exact hk k this
  obtain ⟨j, hj1, hj2⟩ := third_index (σ k) (σ (k + 1)) hne
  refine ⟨j, ?_⟩
  rw [hσ k (k + 1)]
  unfold sideOpp
  rcases opp_eq_of_ne (σ k) (σ (k + 1)) j hj1 hj2 hne with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, dist_comm]

end Erdos634.Geometry
