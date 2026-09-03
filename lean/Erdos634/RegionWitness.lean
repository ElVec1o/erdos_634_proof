import Erdos634.RegionDissection
import Erdos634.Tiling44Bridge

/-!
# A non-degenerate witness for `unionRegion`

`RegionDissection.emptyRegion_disjoint` shows `unionRegion`'s hypothesis is satisfiable, but only by
the *empty* region — a satisfiability check, not a real instance.  This file supplies a real one:
two regions of **positive area** whose interiors are disjoint, taken from an actual congruent
dissection in the corpus (`Tiling44Bridge.dissection`, the `N = 44` witness).

The construction is the obvious one.  A single triangle is a one-tile region dissection; two
distinct tiles of a genuine dissection have disjoint interiors by that dissection's own
`interiors_disjoint`; and each has nonempty interior by `Tri.interior_nonempty`.  So `unionRegion`
applies to them and produces a two-tile region dissection of their union.

This exercises the primitive on real geometry.  It is **not** the collar step: the union of two
tiles of a 44-tiling is not `Δ_{m+2}`, and no claim about `thm:realize12` follows.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.RegionWitness

open Erdos634.Geometry Erdos634.RegionDissection

/-- A single triangle, as a one-tile region dissection. -/
def singleTile (T : Tri) : RegionDissection 1 where
  region := T.carrier
  tile := fun _ => T
  covers := Set.iUnion_const _
  interiors_disjoint := by intro i j hij; exact absurd (Subsingleton.elim i j) hij

@[simp] theorem singleTile_region (T : Tri) : (singleTile T).region = T.carrier := rfl

/-- **Two distinct tiles of any dissection satisfy `unionRegion`'s hypothesis.** -/
theorem tiles_disjoint {N : ℕ} (D : Dissection N) {i j : Fin N} (hij : i ≠ j) :
    Disjoint (interior (singleTile (D.tile i)).region)
      (interior (singleTile (D.tile j)).region) :=
  D.interiors_disjoint hij

/-- **And both regions have nonempty interior** — this is what makes the witness non-degenerate,
as opposed to `emptyRegion_disjoint`. -/
theorem tiles_interior_nonempty {N : ℕ} (D : Dissection N) (i : Fin N) :
    (interior (singleTile (D.tile i)).region).Nonempty :=
  (D.tile i).interior_nonempty

/-- The glued two-tile region dissection, for any two distinct tiles. -/
def glueTiles {N : ℕ} (D : Dissection N) {i j : Fin N} (hij : i ≠ j) : RegionDissection (1 + 1) :=
  unionRegion (singleTile (D.tile i)) (singleTile (D.tile j)) (tiles_disjoint D hij)

@[simp] theorem glueTiles_region {N : ℕ} (D : Dissection N) {i j : Fin N} (hij : i ≠ j) :
    (glueTiles D hij).region = (D.tile i).carrier ∪ (D.tile j).carrier := rfl

/-! ## The concrete instance -/

/-- The `N = 44` congruent dissection has at least two tiles. -/
theorem fortyfour_two_tiles : 1 < Tiling44.tiles.length := by
  simp [Tiling44.tiles]

/-- **The witness.**  Two distinct tiles of the real `N = 44` dissection, glued through
`unionRegion`, with both pieces of positive area. -/
noncomputable def witness : RegionDissection (1 + 1) :=
  glueTiles Tiling44Bridge.dissection.toDissection
    (i := ⟨0, Nat.zero_lt_of_lt fortyfour_two_tiles⟩) (j := ⟨1, fortyfour_two_tiles⟩) (by simp [Fin.ext_iff])

theorem witness_pieces_nonempty :
    (interior (singleTile (Tiling44Bridge.dissection.toDissection.tile ⟨0, Nat.zero_lt_of_lt fortyfour_two_tiles⟩)).region).Nonempty
    ∧ (interior (singleTile
        (Tiling44Bridge.dissection.toDissection.tile ⟨1, fortyfour_two_tiles⟩)).region).Nonempty :=
  ⟨tiles_interior_nonempty _ _, tiles_interior_nonempty _ _⟩

end Erdos634.RegionWitness
