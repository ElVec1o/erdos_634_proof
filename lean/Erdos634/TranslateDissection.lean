import Erdos634.Congruence
import Erdos634.DissectionMap

/-!
# Translating a `CongruentDissection` rigidly

Erdős #634. The collar-induction step for `thm:realize12` needs to place copies of existing
witnesses (`Tiling44Bridge.dissection`, a rescaled `PgramTiling22`) at specific positions inside a
bigger target — pure translations, no rotation, per the hand-derived geometry in
`private/VERIFY_PLAN.md`'s 2026-09-05 entry. `Realizable.scaleDissection` already covers
homothety (scale about a point); this file supplies the companion translation case.

`DissectionMap.mapTri`/`mapDissection` already transport a `Dissection` by any affine equivalence,
and preserve `Tri.Congruent` when the *same* affine equivalence is applied to *both* sides being
compared (`Realizable.mapTri_congruent`, for a homothety-conjugated isometry). What was missing is
the simpler fact needed here: applying an isometry to *one side only* of an existing congruence
still gives a congruence — `Tri.Congruent.map_left`. Translating a whole `CongruentDissection`
(target, every tile, *and* the model, all by the same vector) then preserves `tiles_congruent`
directly, composing the original witness's isometry with the translation's own.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.TranslateDissection

open Erdos634.Geometry Erdos634.DissectionMap

/-- Translation by `v`, as an affine isometry equivalence of the plane. -/
noncomputable def transEquiv (v : Plane) : Plane ≃ᵃⁱ[ℝ] Plane :=
  AffineIsometryEquiv.constVAdd ℝ Plane v

/-- **Applying an isometry to one side of a congruence preserves it.** If `T` is congruent to `U`
and `g` is any affine isometry equivalence, the image of `T` under `g` is still congruent to `U`
(the same fixed reference) — compose `g⁻¹` in front of the original witnessing isometry. -/
theorem _root_.Erdos634.Geometry.Tri.Congruent.map_left {T U : Tri} (h : T.Congruent U)
    (g : Plane ≃ᵃⁱ[ℝ] Plane) : (mapTri g.toAffineEquiv T).Congruent U := by
  obtain ⟨f, σ, hf⟩ := h
  refine ⟨g.toIsometryEquiv.symm.trans f, σ, fun k => ?_⟩
  show f (g.toIsometryEquiv.symm (g.toAffineEquiv (T.pts k))) = U.pts (σ k)
  have hgg : g.toIsometryEquiv.symm (g.toAffineEquiv (T.pts k)) = T.pts k := by
    show g.toIsometryEquiv.symm (g.toIsometryEquiv (T.pts k)) = T.pts k
    exact g.toIsometryEquiv.symm_apply_apply _
  rw [hgg]
  exact hf k

/-- **A whole `CongruentDissection`, translated by a vector `v`.** Target, every tile, and the
model all move by the same translation, so `tiles_congruent` transfers directly via
`Tri.Congruent.map_left`. -/
noncomputable def translateCongruentDissection {N : ℕ} (v : Plane) (D : CongruentDissection N) :
    CongruentDissection N where
  toDissection := mapDissection (transEquiv v).toAffineEquiv D.toDissection
  model := D.model
  tiles_congruent := fun i => by
    rw [mapDissection_tile]
    exact (D.tiles_congruent i).map_left (transEquiv v)

@[simp] theorem translateCongruentDissection_target {N : ℕ} (v : Plane)
    (D : CongruentDissection N) :
    (translateCongruentDissection v D).target = mapTri (transEquiv v).toAffineEquiv D.target :=
  rfl

@[simp] theorem translateCongruentDissection_tile {N : ℕ} (v : Plane) (D : CongruentDissection N)
    (i : Fin N) :
    (translateCongruentDissection v D).tile i = mapTri (transEquiv v).toAffineEquiv (D.tile i) :=
  rfl

end Erdos634.TranslateDissection
