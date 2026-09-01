import Erdos634.ConvexCover

/-!
# Composing dissections: refining each tile by a dissection of its own

Erdős #634. `thm:ladder` — "if `T` is cut into `N` copies of `t`, then `kT` is cut into `k²N`
copies of `t`" — has two halves. `CellCoord.ladderDissection` supplies the first: `kT` really is
cut into `k²` triangles congruent to `T`. This file supplies the second, and it is the general
statement, not the ladder's special case:

> given a `Dissection M` and, for each of its tiles, a `Dissection N` **of that tile**, the `M · N`
> small pieces form a `Dissection (M * N)` of the original target.

This is the *composition map on dissections*, one of the recurring structural blockers named in
`PAPER_MAP`. Every ingredient is already available: `ConvexCover.ofCertificate` reduces the
construction to containment, disjoint interiors and the area identity, and all three are formal
consequences of the two given dissections. In particular no new topology is needed — the covering
comes out of `ofCertificate`'s measure argument, exactly as it does for a search certificate.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.Compose

open Erdos634.Geometry MeasureTheory

variable {M N : ℕ}

/-- A refined piece sits inside the coarse tile it refines. -/
theorem piece_subset (D : Dissection M) (inner : Fin M → Dissection N)
    (hin : ∀ i, ((inner i).target).carrier = (D.tile i).carrier) (i : Fin M) (j : Fin N) :
    ((inner i).tile j).carrier ⊆ (D.tile i).carrier := by
  rw [← hin i]; exact tile_subset_target (inner i) j

/-- Hence its interior sits inside the coarse tile's interior — this is what separates pieces
lying in *different* coarse tiles. -/
theorem piece_interior_subset (D : Dissection M) (inner : Fin M → Dissection N)
    (hin : ∀ i, ((inner i).target).carrier = (D.tile i).carrier) (i : Fin M) (j : Fin N) :
    interior ((inner i).tile j).carrier ⊆ interior (D.tile i).carrier :=
  interior_mono (piece_subset D inner hin i j)

/-- The `M · N` refined pieces, indexed by `Fin (M * N)`. -/
noncomputable def piece (D : Dissection M) (inner : Fin M → Dissection N) (n : Fin (M * N)) : Tri :=
  (inner (finProdFinEquiv.symm n).1).tile (finProdFinEquiv.symm n).2

/-- **Composition of dissections.** If each tile of `D` is itself dissected into `N` pieces, the
`M · N` pieces dissect `D.target`. -/
noncomputable def compose (D : Dissection M) (inner : Fin M → Dissection N)
    (hin : ∀ i, ((inner i).target).carrier = (D.tile i).carrier) : Dissection (M * N) := by
  classical
  refine Erdos634.ConvexCover.ofCertificate D.target (piece D inner) ?_ ?_ ?_
  · -- (C2) containment
    intro n
    exact (piece_subset D inner hin _ _).trans (tile_subset_target D _)
  · -- (C3) disjoint interiors
    intro n m hnm
    by_cases hi : (finProdFinEquiv.symm n).1 = (finProdFinEquiv.symm m).1
    · -- same coarse tile: the inner dissection separates them
      have hj : (finProdFinEquiv.symm n).2 ≠ (finProdFinEquiv.symm m).2 := by
        intro h
        exact hnm (finProdFinEquiv.symm.injective (Prod.ext hi h))
      show Disjoint (interior ((inner _).tile _).carrier) (interior ((inner _).tile _).carrier)
      rw [hi]
      exact (inner _).interiors_disjoint hj
    · -- different coarse tiles: their interiors are already disjoint
      refine Set.disjoint_of_subset (piece_interior_subset D inner hin _ _)
        (piece_interior_subset D inner hin _ _) (D.interiors_disjoint hi)
  · -- (C4) the areas add up
    have hre : ∑ n : Fin (M * N), volume (piece D inner n).carrier
        = ∑ p : Fin M × Fin N, volume ((inner p.1).tile p.2).carrier :=
      Equiv.sum_comp finProdFinEquiv.symm (fun p => volume ((inner p.1).tile p.2).carrier)
    rw [hre, Fintype.sum_prod_type]
    have hrow : ∀ i : Fin M, ∑ j : Fin N, volume ((inner i).tile j).carrier
        = volume (D.tile i).carrier := by
      intro i; rw [← (inner i).volume_target, hin i]
    rw [Finset.sum_congr rfl (fun i _ => hrow i), ← D.volume_target]

@[simp] theorem compose_target (D : Dissection M) (inner : Fin M → Dissection N)
    (hin : ∀ i, ((inner i).target).carrier = (D.tile i).carrier) : (compose D inner hin).target = D.target := rfl

@[simp] theorem compose_tile (D : Dissection M) (inner : Fin M → Dissection N)
    (hin : ∀ i, ((inner i).target).carrier = (D.tile i).carrier) (n : Fin (M * N)) :
    (compose D inner hin).tile n
      = (inner (finProdFinEquiv.symm n).1).tile (finProdFinEquiv.symm n).2 := rfl

end Erdos634.Compose
