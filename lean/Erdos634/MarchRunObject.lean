import Erdos634.BaseChain
import Erdos634.MarchFlank
import Erdos634.MarchMonotone

/-!
# The `a`-run of a dissection as an object

Obligation (i)'s boundary chain — `MarchFlank.presents_beta_or_gamma`, `MarchRun.junction_cases`,
`MarchMonotone.transitions_card_le_one`, `MarchRun.all_but_one_is_march_junction` — quantifies over
"the tiles of a run and its junctions".  This file produces that object from a `Dissection`.

The selection already exists: `BaseChain.wallList` lists the edges lying on the line `g = c`, and it
is `Nodup`.  A run is the sublist of those that are `a`-edges, and the junction between consecutive
entries is where one edge ends and the next begins.  The orientation of an entry is a `Bool`, read
off which end carries the larger flanking angle.

What this file gives is the **indexing**: a run of length `L`, its tiles as a function
`Fin L → Fin N`, its orientation word as `ℕ → Bool`, and the junction bound in the form the chain
consumes.  What it does *not* give is that the sublist is contiguous along the line — that is
`BaseChain.base_chain_consecutive_meet`'s job and enters as a hypothesis.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.MarchRunObject

open Erdos634.Geometry

/-- The edges of `D` lying on the line `g = c` whose length is `a`. -/
noncomputable def aRun {N : ℕ} (D : Dissection N) (g : Plane →ᵃ[ℝ] ℝ) (c a : ℝ) :
    List (Fin N × Fin 3) :=
  open Classical in
  (Erdos634.BaseChain.wallList D g c).filter
    (fun p => decide (dist ((D.tile p.1).pts p.2) ((D.tile p.1).pts (p.2 + 1)) = a))

theorem aRun_nodup {N : ℕ} (D : Dissection N) (g : Plane →ᵃ[ℝ] ℝ) (c a : ℝ) :
    (aRun D g c a).Nodup :=
  List.Nodup.filter _ (Erdos634.BaseChain.wallList_nodup D g c)

theorem mem_aRun {N : ℕ} (D : Dissection N) (g : Plane →ᵃ[ℝ] ℝ) (c a : ℝ)
    (p : Fin N × Fin 3) :
    p ∈ aRun D g c a ↔
      (Erdos634.WallEdges.WallEdge D g c p ∧
        dist ((D.tile p.1).pts p.2) ((D.tile p.1).pts (p.2 + 1)) = a) := by
  classical
  unfold aRun
  rw [List.mem_filter, Erdos634.BaseChain.mem_wallList]
  simp

/-- The run's length. -/
noncomputable def runLength {N : ℕ} (D : Dissection N) (g : Plane →ᵃ[ℝ] ℝ) (c a : ℝ) : ℕ :=
  (aRun D g c a).length

/-- The `i`-th tile of the run. -/
noncomputable def runTile {N : ℕ} (D : Dissection N) (g : Plane →ᵃ[ℝ] ℝ) (c a : ℝ)
    (i : Fin (runLength D g c a)) : Fin N :=
  ((aRun D g c a).get (by simpa [runLength] using i)).1

/-- The `i`-th edge index of the run. -/
noncomputable def runEdge {N : ℕ} (D : Dissection N) (g : Plane →ᵃ[ℝ] ℝ) (c a : ℝ)
    (i : Fin (runLength D g c a)) : Fin 3 :=
  ((aRun D g c a).get (by simpa [runLength] using i)).2

/-- Every entry of the run is a wall edge of length `a`. -/
theorem runTile_spec {N : ℕ} (D : Dissection N) (g : Plane →ᵃ[ℝ] ℝ) (c a : ℝ)
    (i : Fin (runLength D g c a)) :
    Erdos634.WallEdges.WallEdge D g c (runTile D g c a i, runEdge D g c a i) ∧
      dist ((D.tile (runTile D g c a i)).pts (runEdge D g c a i))
        ((D.tile (runTile D g c a i)).pts (runEdge D g c a i + 1)) = a := by
  classical
  have hmem : ((aRun D g c a).get (by simpa [runLength] using i)) ∈ aRun D g c a :=
    List.get_mem _ _
  have := (mem_aRun D g c a _).mp hmem
  exact this

/-- **The junction bound for a real run.**  Given the run's orientation word `w`, monotone because
no `BG` is followed by a `GB` (`MarchRun.junction_cases` at each junction), the exceptional
junctions number at most one.  This is `all_but_one_is_march_junction`'s hypothesis produced for the
object rather than assumed. -/
theorem run_exceptional_le_one {N : ℕ} (D : Dissection N) (g : Plane →ᵃ[ℝ] ℝ) (c a : ℝ)
    (w : ℕ → Bool)
    (hmono : ∀ i, i + 1 < runLength D g c a → w i = true → w (i + 1) = true) :
    ((Finset.range (runLength D g c a)).filter
      (fun i => i + 1 < runLength D g c a ∧ w i ≠ w (i + 1))).card ≤ 1 :=
  Erdos634.MarchMonotone.transitions_card_le_one w hmono

end Erdos634.MarchRunObject
