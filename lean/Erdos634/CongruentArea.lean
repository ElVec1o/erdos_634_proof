import Erdos634.Congruence
import Erdos634.ConvexCover
import Mathlib.Analysis.Normed.Affine.MazurUlam

/-!
# Congruent triangles have equal area

Erdős #634. `Dissection.volume_target_of_congruent` computes the target's volume as `N · v` — but
it takes `hv : ∀ i, volume (tile i).carrier = v` as a **hypothesis**. For a `CongruentDissection`
that hypothesis ought to be free: the tiles are congruent, and congruent sets have equal area. The
corpus never proved it, so every appeal to "the area equation" for a real congruent dissection
carried an undischarged premise.

This file discharges it. `Tri.Congruent` supplies an `IsometryEquiv` of the plane; by Mazur–Ulam
(`IsometryEquiv.toRealLinearIsometryEquiv`) that is a linear isometry followed by a translation,
and both preserve Lebesgue measure (`LinearIsometryEquiv.measurePreserving`,
`measurePreserving_add_right`). Hence `volume_congruent`, and then
`CongruentDissection.volume_target` with no hypothesis at all: the area equation
`|ABC| = N · |T|` holds of any congruent dissection, unconditionally.

This is `prop:dissection`'s second clause for a real congruent dissection, and the area input the
certificate bridge of `ConvexCover` needs on the tile side.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.CongruentArea

open Erdos634.Geometry MeasureTheory
open scoped ENNReal

/-- **An isometry equivalence of the plane preserves Lebesgue measure.** By Mazur–Ulam it is a
linear isometry followed by the translation by `f 0`. -/
theorem measurePreserving_isometryEquiv (f : Plane ≃ᵢ Plane) :
    MeasurePreserving f volume volume := by
  have hdecomp : (f : Plane → Plane) = (fun y => y + f 0) ∘ (f.toRealLinearIsometryEquiv) := by
    funext x
    simp
  have hlin : MeasurePreserving (f.toRealLinearIsometryEquiv) volume volume :=
    LinearIsometryEquiv.measurePreserving _
  have htr : MeasurePreserving (fun y : Plane => y + f 0) volume volume :=
    measurePreserving_add_right volume (f 0)
  rw [show (f : Plane → Plane) = (fun y => y + f 0) ∘ (f.toRealLinearIsometryEquiv) from hdecomp]
  exact htr.comp hlin

/-- **The image of a null-measurable set under an isometry equivalence has the same volume.** -/
theorem volume_image_isometryEquiv (f : Plane ≃ᵢ Plane) (s : Set Plane)
    (hs : NullMeasurableSet s volume) :
    volume (f '' s) = volume s := by
  have himg : f '' s = (f.symm) ⁻¹' s := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩; simpa using hx
    · intro hy; exact ⟨f.symm y, hy, by simp⟩
  rw [himg]
  exact (measurePreserving_isometryEquiv f.symm).measure_preimage hs

/-- **A congruence carries one triangle's carrier onto the other's.** By Mazur–Ulam the isometry is
affine, so it takes convex hulls to convex hulls; the vertex correspondence `σ` then matches the
two vertex sets. -/
theorem image_carrier_of_congruent {T U : Tri} {f : Plane ≃ᵢ Plane} {σ : Equiv.Perm (Fin 3)}
    (hf : ∀ k, f (T.pts k) = U.pts (σ k)) :
    f '' T.carrier = U.carrier := by
  have hpts : f '' (Set.range T.pts) = Set.range U.pts := by
    ext y
    constructor
    · rintro ⟨x, ⟨k, rfl⟩, rfl⟩
      exact ⟨σ k, (hf k).symm⟩
    · rintro ⟨j, rfl⟩
      refine ⟨T.pts (σ.symm j), ⟨σ.symm j, rfl⟩, ?_⟩
      rw [hf (σ.symm j), Equiv.apply_symm_apply]
  have haff : ⇑f.toRealAffineIsometryEquiv.toAffineMap = ⇑f := rfl
  rw [Erdos634.Geometry.Tri.carrier, Erdos634.Geometry.Tri.carrier, ← hpts, ← haff,
    AffineMap.image_convexHull]

/-- **Congruent triangles have equal area.** -/
theorem volume_congruent {T U : Tri} (h : T.Congruent U) :
    volume T.carrier = volume U.carrier := by
  obtain ⟨f, σ, hf⟩ := h
  rw [← image_carrier_of_congruent hf, volume_image_isometryEquiv f _ T.nullMeasurableSet]

/-- **The area equation for a congruent dissection, with no hypothesis.** `|ABC| = N · |T|`, where
`T` is the model tile — `prop:dissection`'s second clause, for a real `CongruentDissection`. -/
theorem congruentDissection_volume_target {N : ℕ} (D : CongruentDissection N) :
    volume D.target.carrier = (N : ℝ≥0∞) * volume D.model.carrier :=
  D.toDissection.volume_target_of_congruent (volume D.model.carrier)
    (fun i => volume_congruent (D.tiles_congruent i))

end Erdos634.CongruentArea
