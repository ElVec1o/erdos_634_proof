import Erdos634.UnionDissection

/-!
# `RegionDissection`: dissections of an arbitrary region, not only of a triangle

The audit of `UnionDissection` (2026-09-04) found its union primitive real but **`Tri`-targeted**:
`hcov` and the result are stated against a triangle, so every piece *and every intermediate union*
must be a triangle.  `thm:realize12`'s collar step cannot be routed through it, because cutting
`Δ_{m+2}` parallel to the base leaves a **trapezoid**, which is not a `Tri` — there is no
`Dissection` of it to feed back in.  That is a type gap, not a missing proof.

This file closes it.  `Dissection` uses its `target` only through `target.carrier`, so replacing
the field by a bare `Set Plane` costs nothing and buys closure under union:

* `RegionDissection` / `CongruentRegionDissection` — the same data over a region.
* `Dissection.toRegion` / `CongruentDissection.toRegion` — every triangle dissection is one.
* `unionRegion` / `unionCongruentRegion` — **closed under gluing**: no ambient triangle is
  required, so trapezoids, collars and their partial unions are all legitimate intermediates.
* `CongruentRegionDissection.toCongruentDissection` — the exit map: once the accumulated region
  *is* a triangle's carrier, a genuine `CongruentDissection` comes back out.

Together these make the collar induction expressible: glue pieces in any order through regions, and
exit to a `CongruentDissection` at the end.  What is still **not** here is any concrete collar — the
geometry of the parallelogram columns and the corner piece, and the proofs that their carriers have
disjoint interiors and union correctly.  That remains the tile-placement blocker.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.RegionDissection

open Erdos634.Geometry

variable {M N : ℕ}

/-- A dissection of an arbitrary planar region into `N` triangles. -/
structure RegionDissection (N : ℕ) where
  /-- The region being dissected — a set, not necessarily a triangle. -/
  region : Set Plane
  /-- The tiles. -/
  tile : Fin N → Tri
  /-- The tiles cover the region and nothing more. -/
  covers : (⋃ i, (tile i).carrier) = region
  /-- Distinct tiles have disjoint interiors. -/
  interiors_disjoint :
    Pairwise fun i j => Disjoint (interior (tile i).carrier) (interior (tile j).carrier)

/-- Every triangle dissection is a region dissection. -/
def _root_.Erdos634.Geometry.Dissection.toRegion (D : Dissection N) : RegionDissection N where
  region := D.target.carrier
  tile := D.tile
  covers := D.covers
  interiors_disjoint := D.interiors_disjoint

namespace RegionDissection

/-- A tile's interior sits inside the region's interior. -/
theorem tile_interior_subset (R : RegionDissection N) (i : Fin N) :
    interior (R.tile i).carrier ⊆ interior R.region :=
  interior_mono (by rw [← R.covers]; exact Set.subset_iUnion (fun k => (R.tile k).carrier) i)

end RegionDissection

/-- **Gluing two region dissections.**  No ambient triangle: the result is a dissection of the
union, so partial unions of a collar are themselves legitimate inputs. -/
def unionRegion (R1 : RegionDissection M) (R2 : RegionDissection N)
    (hdisj : Disjoint (interior R1.region) (interior R2.region)) :
    RegionDissection (M + N) where
  region := R1.region ∪ R2.region
  tile := Fin.append R1.tile R2.tile
  covers := by
    rw [← R1.covers, ← R2.covers]
    ext x
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨i, hi⟩
      induction i using Fin.addCases with
      | left j => left; exact ⟨j, by rwa [Fin.append_left] at hi⟩
      | right j => right; exact ⟨j, by rwa [Fin.append_right] at hi⟩
    · rintro (⟨j, hj⟩ | ⟨j, hj⟩)
      · exact ⟨Fin.castAdd N j, by rwa [Fin.append_left]⟩
      · exact ⟨Fin.natAdd M j, by rwa [Fin.append_right]⟩
  interiors_disjoint := by
    intro i j hij
    induction i using Fin.addCases with
    | left i' =>
      induction j using Fin.addCases with
      | left j' =>
        simp only [Fin.append_left]; exact R1.interiors_disjoint (by simpa using hij)
      | right j' =>
        simp only [Fin.append_left, Fin.append_right]
        exact hdisj.mono (R1.tile_interior_subset i') (R2.tile_interior_subset j')
    | right i' =>
      induction j using Fin.addCases with
      | left j' =>
        simp only [Fin.append_left, Fin.append_right]
        exact hdisj.symm.mono (R2.tile_interior_subset i') (R1.tile_interior_subset j')
      | right j' =>
        simp only [Fin.append_right]; exact R2.interiors_disjoint (by simpa using hij)

@[simp] theorem unionRegion_region (R1 : RegionDissection M) (R2 : RegionDissection N)
    (hdisj : Disjoint (interior R1.region) (interior R2.region)) :
    (unionRegion R1 R2 hdisj).region = R1.region ∪ R2.region := rfl

theorem unionRegion_tile_left (R1 : RegionDissection M) (R2 : RegionDissection N)
    (hdisj : Disjoint (interior R1.region) (interior R2.region)) (i : Fin M) :
    (unionRegion R1 R2 hdisj).tile (Fin.castAdd N i) = R1.tile i := Fin.append_left _ _ i

theorem unionRegion_tile_right (R1 : RegionDissection M) (R2 : RegionDissection N)
    (hdisj : Disjoint (interior R1.region) (interior R2.region)) (i : Fin N) :
    (unionRegion R1 R2 hdisj).tile (Fin.natAdd M i) = R2.tile i := Fin.append_right _ _ i

/-! ## The congruent version, and the exit map -/

/-- A region dissection all of whose tiles are congruent to one model. -/
structure CongruentRegionDissection (N : ℕ) extends RegionDissection N where
  /-- The common shape. -/
  model : Tri
  /-- Every tile is congruent to it. -/
  tiles_congruent : ∀ i, (tile i).Congruent model

/-- Every congruent triangle dissection is a congruent region dissection. -/
def _root_.Erdos634.Geometry.CongruentDissection.toRegion (D : CongruentDissection N) :
    CongruentRegionDissection N where
  toRegionDissection := D.toDissection.toRegion
  model := D.model
  tiles_congruent := D.tiles_congruent

/-- **Gluing two same-model congruent region dissections.** -/
def unionCongruentRegion (C1 : CongruentRegionDissection M) (C2 : CongruentRegionDissection N)
    (hmodel : C1.model = C2.model)
    (hdisj : Disjoint (interior C1.region) (interior C2.region)) :
    CongruentRegionDissection (M + N) where
  toRegionDissection := unionRegion C1.toRegionDissection C2.toRegionDissection hdisj
  model := C1.model
  tiles_congruent := by
    intro i
    induction i using Fin.addCases with
    | left i' => rw [unionRegion_tile_left]; exact C1.tiles_congruent i'
    | right i' => rw [unionRegion_tile_right, hmodel]; exact C2.tiles_congruent i'

/-- **The exit map.**  Once the accumulated region is a triangle's carrier, a genuine
`CongruentDissection` of that triangle comes back out.  This is what lets a collar induction glue
through non-triangular intermediates and still land on the target type. -/
def CongruentRegionDissection.toCongruentDissection (C : CongruentRegionDissection N) (T : Tri)
    (hT : C.region = T.carrier) : CongruentDissection N where
  target := T
  tile := C.tile
  covers := by rw [C.covers, hT]
  interiors_disjoint := C.interiors_disjoint
  model := C.model
  tiles_congruent := C.tiles_congruent

/-! ## Coherence and a vacuity check -/

/-- **Roundtrip.**  A congruent triangle dissection, viewed as a region dissection and exited again
at its own target, is the one it started as.  This pins the two maps as mutually inverse on the
triangle case, so nothing is lost by working through regions. -/
theorem toRegion_toCongruentDissection (D : CongruentDissection N) :
    D.toRegion.toCongruentDissection D.target rfl = D := rfl

/-- The empty region, dissected into no tiles. -/
def emptyRegion : RegionDissection 0 where
  region := ∅
  tile := fun i => absurd i.isLt (by omega)
  covers := by simp
  interiors_disjoint := by intro i; exact absurd i.isLt (by omega)

/-- **Vacuity check on `unionRegion`'s hypothesis.**  `Disjoint (interior R1.region)
(interior R2.region)` is satisfiable: the empty region meets nothing.  This is deliberately
*degenerate* — it shows the hypothesis is not self-contradictory, nothing more.  A non-degenerate
witness (two positive-area pieces of a real collar) needs the tile-placement layer and is not here;
saying otherwise would be the `False → False` mistake this project has already made twice. -/
theorem emptyRegion_disjoint (R : RegionDissection N) :
    Disjoint (interior R.region) (interior emptyRegion.region) := by
  simp [emptyRegion]

/-- Gluing the empty region on changes nothing but the index count. -/
@[simp] theorem unionRegion_empty (R : RegionDissection N) :
    (unionRegion R emptyRegion (emptyRegion_disjoint R)).region = R.region := by
  simp [emptyRegion]

end Erdos634.RegionDissection
