import Erdos634.CongruentArea
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Determinant

/-!
# Areas from coordinates: the arithmetic half of the certified-search bridge

Erdős #634. `ConvexCover.ofCertificate` reduces building a `Dissection` to (C2) containment,
(C3) disjoint interiors and (C4) the area identity `∑ᵢ |tᵢ| = |T|`. A search certificate checks
(C4) in **exact arithmetic on coordinates**, as a sum of determinants. The `PAPER_MAP` rows for
`thm:44`, `thm:63`, `cor:elevenm`, `thm:frontier`–`thm:frontier4` and `thm:eq105` all recorded the
missing passage as "`volume (Tri) = |det| / 2`, absent from this corpus and from Mathlib".

**That is not what is needed.** The constant is irrelevant: only the *ratio* of areas ever enters
(C4), so the area of the reference triangle cancels and never has to be evaluated. What is needed
is only

  `volume T.carrier = ENNReal.ofReal |det T| * volume S₀`

for a fixed reference set `S₀`, and that is `Measure.addHaar_image_linearMap` plus translation
invariance: `T` is the image of `S₀` under `x ↦ (edgeMap T) x + T.pts 0`, where `edgeMap T` sends
the standard basis to `T`'s two edge vectors at vertex `0`.

`volume_eq_det_mul` is that identity, `detTri_eq` gives the determinant in the coordinate form a
certificate computes, and `area_identity_of_det` is the payoff: **(C4) follows from the exact
integer identity `∑ᵢ |det tᵢ| = |det T|` alone**, with no measure theory left in the certificate.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.AreaDet

open Erdos634.Geometry MeasureTheory

/-- The standard basis of the plane, as a `Basis`. -/
noncomputable def pb : Module.Basis (Fin 2) ℝ Plane := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis

/-- The linear map sending the standard basis to `T`'s two edge vectors at vertex `0`. -/
noncomputable def edgeMap (T : Tri) : Plane →ₗ[ℝ] Plane :=
  pb.constr ℝ (fun i : Fin 2 => T.pts i.succ - T.pts 0)

/-- The determinant of a triangle: twice its signed area. -/
noncomputable def detTri (T : Tri) : ℝ := LinearMap.det (edgeMap T)

/-- The reference triangle's carrier: the convex hull of `0` and the two standard basis vectors. -/
noncomputable def stdCarrier : Set Plane :=
  convexHull ℝ (Set.range ![(0 : Plane), pb 0, pb 1])

/-- The affine map carrying the reference triangle onto `T`. -/
noncomputable def placeMap (T : Tri) : Plane →ᵃ[ℝ] Plane :=
  (AffineEquiv.constVAdd ℝ Plane (T.pts 0)).toAffineMap.comp (edgeMap T).toAffineMap

theorem placeMap_apply (T : Tri) (x : Plane) : placeMap T x = T.pts 0 + edgeMap T x := by
  simp [placeMap, AffineEquiv.constVAdd, vadd_eq_add]

theorem edgeMap_basis (T : Tri) (i : Fin 2) : edgeMap T (pb i) = T.pts i.succ - T.pts 0 := by
  simp [edgeMap, Module.Basis.constr_basis]

/-- The affine map carries the reference vertices onto `T`'s vertices. -/
theorem placeMap_range (T : Tri) :
    (placeMap T) '' (Set.range ![(0 : Plane), pb 0, pb 1]) = Set.range T.pts := by
  have htri : ∀ y : Fin 3, y = 0 ∨ y = 1 ∨ y = 2 := by decide
  have hv : ∀ i : Fin 3, placeMap T (![(0 : Plane), pb 0, pb 1] i) = T.pts i := by
    intro i
    rcases htri i with rfl | rfl | rfl
    · show placeMap T 0 = T.pts 0
      simp [placeMap_apply]
    · show placeMap T (pb 0) = T.pts 1
      rw [placeMap_apply, edgeMap_basis]
      show T.pts 0 + (T.pts 1 - T.pts 0) = T.pts 1
      abel
    · show placeMap T (pb 1) = T.pts 2
      rw [placeMap_apply, edgeMap_basis]
      show T.pts 0 + (T.pts 2 - T.pts 0) = T.pts 2
      abel
  rw [← Set.range_comp]
  exact congrArg Set.range (funext hv)

/-- **The reference triangle is carried onto `T`.** -/
theorem placeMap_stdCarrier (T : Tri) : (placeMap T) '' stdCarrier = T.carrier := by
  rw [stdCarrier, AffineMap.image_convexHull, placeMap_range, Erdos634.Geometry.Tri.carrier]

/-- **Area from the determinant, up to one universal constant.** -/
theorem volume_eq_det_mul (T : Tri) :
    volume T.carrier = ENNReal.ofReal |detTri T| * volume stdCarrier := by
  rw [← placeMap_stdCarrier T]
  have hcomp : (placeMap T) '' stdCarrier
      = (fun h => T.pts 0 + h) '' (edgeMap T '' stdCarrier) := by
    rw [← Set.image_comp]
    exact congrArg (· '' stdCarrier) (funext fun x => placeMap_apply T x)
  have hpre : (fun h : Plane => T.pts 0 + h) '' (edgeMap T '' stdCarrier)
      = (fun h : Plane => (-T.pts 0) + h) ⁻¹' (edgeMap T '' stdCarrier) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩; simpa using hx
    · intro hy; exact ⟨(-T.pts 0) + y, hy, by abel⟩
  rw [hcomp, hpre, measure_preimage_add, Measure.addHaar_image_linearMap]
  rfl

/-- The basis coordinates of the plane are the coordinates. -/
theorem pb_repr (v : Plane) (i : Fin 2) : pb.repr v i = v i := by
  simp [pb]

/-- **The determinant in coordinates** — the quantity a certificate computes in exact arithmetic. -/
theorem detTri_eq (T : Tri) :
    detTri T = (T.pts 1 - T.pts 0) 0 * (T.pts 2 - T.pts 0) 1
             - (T.pts 2 - T.pts 0) 0 * (T.pts 1 - T.pts 0) 1 := by
  rw [detTri, ← LinearMap.det_toMatrix pb, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, edgeMap_basis, pb_repr]

/-- **(C4) from exact arithmetic alone.** If the pieces' determinants sum in absolute value to the
target's, their areas sum to the target's — no measure theory left on the certificate side. -/
theorem area_identity_of_det {N : ℕ} (target : Tri) (tile : Fin N → Tri)
    (h : ∑ i, |detTri (tile i)| = |detTri target|) :
    ∑ i, volume (tile i).carrier = volume target.carrier := by
  simp only [volume_eq_det_mul]
  rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _), h]

/-- **A `Dissection` from a fully arithmetic certificate.** (C2) containment and (C3) disjoint
interiors, plus the *exact determinant identity* (C4). This is the certified-search bridge with
no analytic content on the certificate side. -/
noncomputable def ofDetCertificate {N : ℕ} (target : Tri) (tile : Fin N → Tri)
    (hsub : ∀ i, (tile i).carrier ⊆ target.carrier)
    (hdisj : Pairwise fun i j =>
      Disjoint (interior (tile i).carrier) (interior (tile j).carrier))
    (hdet : ∑ i, |detTri (tile i)| = |detTri target|) :
    Dissection N :=
  Erdos634.ConvexCover.ofCertificate target tile hsub hdisj
    (area_identity_of_det target tile hdet)

end Erdos634.AreaDet
