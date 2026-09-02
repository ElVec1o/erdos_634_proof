import Erdos634.ConvexCover

/-!
# The covering-from-volume argument, generalized past `Tri` targets

Erdős #634. `ConvexCover.covers_of_volume` proves that containment, disjoint interiors and the
exact area identity force a family of `Tri` pieces to cover a `Tri` target, not just sit inside
it — but its own proof, checked directly, never actually uses `target.carrier`'s `Tri` structure,
only four facts about it: convex, compact, nonempty interior, finite volume.
`PgramTiling22Bridge.covers_of_volume` already noticed this (its own docstring: "none of which was
actually triangle-specific") and re-proved the same argument by hand for its one fixed
parallelogram target, rather than reusing a general statement — because none existed.

`covers_of_volume_general` extracts the general statement, over any `Set Plane` satisfying those
four properties. `ConvexCover.covers_of_volume` becomes a one-line corollary. This is the tool
needed to cover a non-`Tri` target (a parallelogram, a grid of bricks, …) — such as `lem:wpgram`'s
general-`f` W-parallelogram — without re-deriving the measure argument by hand each time, the way
`PgramTiling22Bridge` had to.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry MeasureTheory

/-- **General covering-from-volume**, for any convex compact target with nonempty interior and
finite volume — not just a `Tri`. -/
theorem covers_of_volume_general {N : ℕ} {S : Set Plane} (hSconv : Convex ℝ S)
    (hScompact : IsCompact S) (hSint : (interior S).Nonempty) (hSvol : volume S ≠ ⊤)
    (tile : Fin N → Tri)
    (hsub : ∀ i, (tile i).carrier ⊆ S)
    (hdisj : Pairwise fun i j => Disjoint (interior (tile i).carrier) (interior (tile j).carrier))
    (hvol : ∑ i, volume (tile i).carrier = volume S) :
    (⋃ i, (tile i).carrier) = S := by
  classical
  set U : Set Plane := ⋃ i, (tile i).carrier with hUdef
  have hUsub : U ⊆ S := Set.iUnion_subset hsub
  have hUvol : volume U = volume S := by
    rw [hUdef, Erdos634.ConvexCover.volume_iUnion_eq_sum tile hdisj, hvol]
  have hUclosed : IsClosed U := by
    rw [hUdef]; exact isClosed_iUnion_of_finite fun i => (tile i).isCompact.isClosed
  refine Set.Subset.antisymm hUsub ?_
  by_contra hcon
  obtain ⟨x, hxT, hxU⟩ : ∃ x, x ∈ S ∧ x ∉ U := by
    by_contra hall; push_neg at hall; exact hcon fun x hx => hall x hx
  have hVopen : IsOpen (Uᶜ) := hUclosed.isOpen_compl
  have hxcl : x ∈ closure (interior S) := by
    have hclosed : IsClosed S := hScompact.isClosed
    have := hSconv.closure_interior_eq_closure_of_nonempty_interior hSint
    rw [this, hclosed.closure_eq]; exact hxT
  obtain ⟨y, hyV, hyI⟩ : ∃ y, y ∈ Uᶜ ∧ y ∈ interior S :=
    mem_closure_iff.mp hxcl (Uᶜ) hVopen hxU
  set W : Set Plane := Uᶜ ∩ interior S with hWdef
  have hWopen : IsOpen W := hVopen.inter isOpen_interior
  have hWne : W.Nonempty := ⟨y, hyV, hyI⟩
  have hWpos : 0 < volume W := hWopen.measure_pos volume hWne
  have hWsub : W ⊆ S := fun z hz => interior_subset hz.2
  have hWdisj : Disjoint U W := Set.disjoint_right.mpr fun z hz => hz.1
  have hsum : volume U + volume W ≤ volume S := by
    have hunion : volume (U ∪ W) = volume U + volume W :=
      measure_union₀ hWopen.measurableSet.nullMeasurableSet hWdisj.aedisjoint
    rw [← hunion]; exact measure_mono (Set.union_subset hUsub hWsub)
  rw [hUvol] at hsum
  have : volume S + 0 < volume S + volume W :=
    ENNReal.add_lt_add_left hSvol hWpos
  simp only [add_zero] at this
  exact absurd hsum (not_le.mpr this)

/-- `ConvexCover.covers_of_volume`, now a corollary of the general statement. -/
theorem covers_of_volume_tri {N : ℕ} (target : Tri) (tile : Fin N → Tri)
    (hsub : ∀ i, (tile i).carrier ⊆ target.carrier)
    (hdisj : Pairwise fun i j => Disjoint (interior (tile i).carrier) (interior (tile j).carrier))
    (hvol : ∑ i, volume (tile i).carrier = volume target.carrier) :
    (⋃ i, (tile i).carrier) = target.carrier :=
  covers_of_volume_general (by rw [Erdos634.Geometry.Tri.carrier]; exact convex_convexHull ℝ _)
    target.isCompact target.interior_nonempty target.volume_ne_top tile hsub hdisj hvol
