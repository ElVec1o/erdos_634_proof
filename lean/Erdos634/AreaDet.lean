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

/-! ## Toward `volume stdCarrier = 1/2`

Needed for non-`Tri` targets whose reference measure is a *square*, not `stdCarrier` itself (see
`Erdos634.PgramTiling22Bridge`): `stdCarrier` is exactly half of the unit square `[0,1]²`, split by
its diagonal, so its volume is `1/2`. The two pieces below build the volume-preserving point
reflection through the square's center and identify its image of `stdCarrier` as the mirror
triangle; what remains (not yet done) is showing the two triangles' union is exactly the unit
square and their interiors are disjoint, then combining via measure additivity. -/

/-- The square's center, `pb 0 + pb 1`. -/
noncomputable def reflC : Plane := pb 0 + pb 1

/-- Point reflection through `reflC`. -/
noncomputable def reflMap (x : Plane) : Plane := reflC - x

/-- **Point reflection preserves volume** — negation has determinant `1` in even dimension (here
`2`), so `Measure.addHaar_image_linearMap` gives back the same volume, and translation invariance
(the same step `volume_carrier_eq` uses) removes the constant shift. -/
theorem volume_neg_image (S : Set Plane) :
    volume ((fun x : Plane => -x) '' S) = volume S := by
  have hcomp : (fun x : Plane => -x) '' S = (-LinearMap.id : Plane →ₗ[ℝ] Plane) '' S := by
    ext y; simp
  rw [hcomp, Measure.addHaar_image_linearMap]
  rw [show LinearMap.det (-LinearMap.id : Plane →ₗ[ℝ] Plane) = 1 by
    rw [show (-LinearMap.id : Plane →ₗ[ℝ] Plane) = (-1:ℝ) • LinearMap.id by ext x; simp,
      LinearMap.det_smul]; simp]
  simp

theorem volume_reflMap_image (S : Set Plane) : volume (reflMap '' S) = volume S := by
  have hfun : reflMap = (fun y : Plane => reflC + y) ∘ (fun x : Plane => -x) := by
    funext x
    show reflC - x = reflC + (-x)
    abel
  rw [show reflMap '' S = (fun y : Plane => reflC + y) '' ((fun x : Plane => -x) '' S) from
    hfun ▸ Set.image_comp _ _ S]
  have hpre : (fun y : Plane => reflC + y) '' ((fun x : Plane => -x) '' S)
      = (fun y : Plane => (-reflC) + y) ⁻¹' ((fun x : Plane => -x) '' S) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩; simpa using hx
    · intro hy; exact ⟨(-reflC) + y, hy, by abel⟩
  rw [hpre, measure_preimage_add, volume_neg_image]

/-- `reflMap`, as a genuine affine map (needed for `AffineMap.image_convexHull`). -/
noncomputable def reflAff : Plane →ᵃ[ℝ] Plane :=
  (AffineEquiv.constVAdd ℝ Plane reflC).toAffineMap.comp
    ((-LinearMap.id : Plane →ₗ[ℝ] Plane).toAffineMap)

theorem reflAff_apply (x : Plane) : reflAff x = reflC - x := by
  show reflC +ᵥ (-x) = reflC - x
  rw [vadd_eq_add]; abel

theorem reflAff_eq_reflMap : (reflAff : Plane → Plane) = reflMap := by
  funext x; rw [reflAff_apply]; rfl

/-- **The reflection of `stdCarrier` is the mirror triangle** spanning `reflC`, `pb 1`, `pb 0`
(since `reflC - pb 0 = pb 1` and `reflC - pb 1 = pb 0`). -/
theorem reflMap_stdCarrier :
    reflMap '' stdCarrier = convexHull ℝ (Set.range ![reflC, pb 1, pb 0]) := by
  rw [← reflAff_eq_reflMap, stdCarrier, AffineMap.image_convexHull]
  congr 1
  rw [← Set.range_comp]
  apply congrArg Set.range
  funext i
  fin_cases i
  · show reflAff 0 = reflC
    rw [reflAff_apply]; abel
  · show reflAff (pb 0) = pb 1
    rw [reflAff_apply]
    show reflC - pb 0 = pb 1
    show (pb 0 + pb 1) - pb 0 = pb 1
    abel
  · show reflAff (pb 1) = pb 0
    rw [reflAff_apply]
    show reflC - pb 1 = pb 0
    show (pb 0 + pb 1) - pb 1 = pb 0
    abel

/-- The mirror triangle: the "other half" of the unit square. -/
noncomputable def stdCarrier2 : Set Plane := convexHull ℝ (Set.range ![reflC, pb 1, pb 0])

/-- **`stdCarrier` and its mirror have equal volume**, by the volume-preserving reflection. -/
theorem volume_stdCarrier2_eq : volume stdCarrier2 = volume stdCarrier := by
  rw [stdCarrier2, ← reflMap_stdCarrier, volume_reflMap_image]

/-! **Still open**: `stdCarrier ∪ stdCarrier2 = {x : Plane | x 0 ∈ Set.Icc (0:ℝ) 1 ∧
x 1 ∈ Set.Icc (0:ℝ) 1}` (the unit square) with disjoint interiors, which combined with
`volume_stdCarrier2_eq` and the square's volume `1` (see
`Erdos634.PgramTiling22Bridge.volume_stdSquare` for that computation, on a square defined the same
way) would give `volume stdCarrier = 1/2` by measure additivity. What remains: a coordinate
characterization of `stdCarrier`'s membership (`x ∈ stdCarrier ↔ 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤
1`) — the ⊇ direction follows from `x = x 0 • pb 0 + x 1 • pb 1` (`Basis.sum_repr` plus `pb_repr`,
already available) giving an explicit barycentric combination directly; the ⊆ direction needs
either building `stdCarrier` as a genuine `Tri.carrier` (requiring `AffineIndependent ℝ ![0, pb 0,
pb 1]`, not yet proven anywhere in this corpus) to reuse `Tri.carrier_eq_nonneg_coord`, or a direct
convexity argument that the three points all satisfy the halfplane inequalities and those
inequalities cut out a convex set.
-/

end Erdos634.AreaDet
