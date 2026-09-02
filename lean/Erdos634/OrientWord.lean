import Erdos634.OrientBridge
import Erdos634.RunOrientation

/-!
# The orientation word of the base chain

Erdős #634, bridge (c), the last piece.  `BaseChain.base_chain_consecutive_meet` orders the base
chain; `OrientBridge.adjacent_admissible` forbids two `γ`s at a shared junction of a real
dissection; `RunOrientation.corner_anchored_run_all_BG` consumes a *word* — a list of orientations
whose adjacent pairs are admissible.

This file builds that word from the ordered chain and proves it is a chain in the required sense.
Its hypotheses are per-junction: that consecutive chain edges share a point of the frontier which
is not a target vertex, that consecutive edges belong to distinct tiles, and the two readings
`orient_BG_east_gamma` and `orient_GB_west_gamma` supply.  With the word in hand the combinatorial
march theorems apply to a dissection.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.OrientWord

open Erdos634.Geometry Erdos634.Inflation List

/-- The orientation word of a chain of `n` tiles, read in order. -/
def word (n : ℕ) (o : ℕ → Orient) : List Orient := (List.range n).map o

theorem word_length (n : ℕ) (o : ℕ → Orient) : (word n o).length = n := by
  simp [word]

/-- **Reading off a constant word.** If `word n o` is `replicate n c`, every one of its indices
`m < n` has `o m = c`. Needed to turn `thm:chain`-style "the word is constant" conclusions
(e.g. `BEdgeReading.side_word_constant`) into a per-edge fact. -/
theorem word_apply {n : ℕ} {o : ℕ → Orient} {c : Orient} (h : word n o = List.replicate n c)
    (m : ℕ) (hm : m < n) : o m = c := by
  have hmem : o m ∈ word n o := by
    rw [word]
    exact List.mem_map_of_mem (List.mem_range.mpr hm)
  rw [h] at hmem
  exact List.eq_of_mem_replicate hmem

/-- **The word is admissible.**  If at every junction of the chain the two tiles are distinct, the
junction is a non-vertex point of the frontier, and the two readings hold, then adjacent letters of
the word satisfy `admissiblePair`.

This is `OrientBridge.adjacent_admissible` quantified along the chain. -/
theorem word_isChain {N : ℕ} (D : Dissection N) (n : ℕ) (o : ℕ → Orient) (tile : ℕ → Fin N)
    (p : ℕ → Plane) (α β γ : ℝ) (hα : 0 < α) (hγ : γ = 2 * α + β)
    (hπ : 3 * α + 2 * β = Real.pi)
    (hfront : ∀ j, j + 1 < n → p j ∈ frontier D.target.carrier)
    (hvert : ∀ j, j + 1 < n → p j ∉ Set.range D.target.pts)
    (hne : ∀ j, j + 1 < n → tile j ≠ tile (j + 1))
    (hBG : ∀ j, j + 1 < n → o j = Orient.BG → (D.tile (tile j)).localAngle (p j) = γ)
    (hGB : ∀ j, j + 1 < n → o (j + 1) = Orient.GB →
      (D.tile (tile (j + 1))).localAngle (p j) = γ) :
    (word n o).IsChain (fun l r => admissiblePair l r = true) := by
  rw [word, List.isChain_iff_getElem]
  intro i hi
  rw [List.length_map, List.length_range] at hi
  simp only [List.getElem_map, List.getElem_range]
  exact Erdos634.OrientBridge.adjacent_admissible D (hfront i hi) (hvert i hi) α β γ hα hγ hπ
    (tile i) (tile (i + 1)) (hne i hi) (o i) (o (i + 1)) (hBG i hi) (hGB i hi)

/-- **The word of a corner-anchored chain is constant.**  Combining with
`RunOrientation.corner_anchored_run_all_BG`: a chain whose first tile shows `β` at the target's
corner has every tile showing `β` west and `γ` east.  That is the orientation propagation the
march needs, now for a word read off a dissection. -/
theorem corner_anchored_word {N : ℕ} (D : Dissection N) (n : ℕ) (o : ℕ → Orient) (tile : ℕ → Fin N)
    (p : ℕ → Plane) (α β γ : ℝ) (hα : 0 < α) (hγ : γ = 2 * α + β)
    (hπ : 3 * α + 2 * β = Real.pi)
    (hfront : ∀ j, j + 1 < n → p j ∈ frontier D.target.carrier)
    (hvert : ∀ j, j + 1 < n → p j ∉ Set.range D.target.pts)
    (hne : ∀ j, j + 1 < n → tile j ≠ tile (j + 1))
    (hBG : ∀ j, j + 1 < n → o j = Orient.BG → (D.tile (tile j)).localAngle (p j) = γ)
    (hGB : ∀ j, j + 1 < n → o (j + 1) = Orient.GB →
      (D.tile (tile (j + 1))).localAngle (p j) = γ)
    (hseed : (word n o).head? = some Orient.BG) :
    word n o = List.replicate (word n o).length Orient.BG :=
  Erdos634.RunOrientation.corner_anchored_run_all_BG (word n o)
    (word_isChain D n o tile p α β γ hα hγ hπ hfront hvert hne hBG hGB) hseed

end Erdos634.OrientWord
