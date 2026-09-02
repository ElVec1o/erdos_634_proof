import Erdos634.CollarContainM4
import Erdos634.AreaDet

/-!
# The `m=2 → m=4` collar step — area transport under placement maps

Erdős #634. `thm:realize12`'s existence half needs, as its third ingredient (C4), the area-sum
identity for `Δ_4`'s 176-piece certificate: the pieces' `|detTri|` values must sum to `|detTri
delta4|`. Every piece reaches its final position via `mapTri` composed with either a translation
(`TranslateDissection.transEquiv`) or a homothety (`Realizable.homothetyEquiv`, ratio `2`, used for
the column pieces), so this file builds the general fact needed to transport `AreaDet.detTri`
through those maps: `detTri (mapTri e T) = LinearMap.det e.linear * detTri T`, then specializes it
to translation (`det = 1`, area unchanged) and to the ratio-`r` homothety (`det = r²`, area scaled
by `r²`).

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.CertCoord Erdos634.DissectionMap Erdos634.AreaDet
open Erdos634.Realizable

/-- `edgeMap` transports through `mapTri e` by post-composing with `e`'s linear part. -/
theorem edgeMap_mapTri (e : Plane ≃ᵃ[ℝ] Plane) (T : Tri) :
    edgeMap (mapTri e T) = (e.linear : Plane →ₗ[ℝ] Plane).comp (edgeMap T) := by
  apply pb.ext
  intro i
  rw [LinearMap.comp_apply, edgeMap_basis, edgeMap_basis]
  show e (T.pts i.succ) - e (T.pts 0) = e.linear (T.pts i.succ - T.pts 0)
  rw [← vsub_eq_sub, ← vsub_eq_sub]
  exact (AffineMap.linearMap_vsub e.toAffineMap _ _).symm

/-- **Area transport under an affine equivalence**: `mapTri e` scales `detTri` by `det e.linear`. -/
theorem detTri_mapTri (e : Plane ≃ᵃ[ℝ] Plane) (T : Tri) :
    detTri (mapTri e T) = LinearMap.det (e.linear : Plane →ₗ[ℝ] Plane) * detTri T := by
  rw [detTri, edgeMap_mapTri, LinearMap.det_comp, detTri]

theorem homothetyEquiv_linear (p : Plane) (r : ℝ) (hr : r ≠ 0) :
    ((homothetyEquiv p r hr).linear : Plane →ₗ[ℝ] Plane) = r • LinearMap.id := by
  have h1 : (homothetyEquiv p r hr : Plane →ᵃ[ℝ] Plane) = AffineMap.homothety p r := by
    apply AffineMap.ext
    intro x
    exact congrFun (AffineEquiv.coe_homothetyUnitsMulHom_apply p (Units.mk0 r hr)) x
  have h2 := congrArg AffineMap.linear h1
  rw [AffineMap.homothety_linear] at h2
  exact h2

/-- A homothety of ratio `r` has linear-part determinant `r²` (2-dimensional `Plane`). -/
theorem homothety_linear_det (p : Plane) (r : ℝ) (hr : r ≠ 0) :
    LinearMap.det ((homothetyEquiv p r hr).linear : Plane →ₗ[ℝ] Plane) = r ^ 2 := by
  rw [homothetyEquiv_linear, LinearMap.det_smul]
  simp

/-- **A homothety of ratio `r` scales `detTri` (hence area) by `r²`.** Used for the column pieces,
placed via the ratio-`2` homothety, so their area scales by `4`. -/
theorem detTri_homothetyEquiv (p : Plane) (r : ℝ) (hr : r ≠ 0) (T : Tri) :
    detTri (mapTri (homothetyEquiv p r hr) T) = r ^ 2 * detTri T := by
  rw [detTri_mapTri, homothety_linear_det]

theorem transEquiv_linear (v : Plane) :
    ((Erdos634.TranslateDissection.transEquiv v).toAffineEquiv.linear : Plane →ₗ[ℝ] Plane) =
      LinearMap.id := by
  unfold Erdos634.TranslateDissection.transEquiv
  rfl

/-- **A translation preserves `detTri` (hence area) exactly.** Used for the apex and corner
pieces, both placed by pure translation. -/
theorem detTri_transEquiv (v : Plane) (T : Tri) :
    detTri (mapTri (Erdos634.TranslateDissection.transEquiv v).toAffineEquiv T) = detTri T := by
  rw [detTri_mapTri, transEquiv_linear, LinearMap.det_id, one_mul]
