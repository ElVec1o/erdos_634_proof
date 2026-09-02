import Erdos634.CongruentArea
import Erdos634.InteriorCoord
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

/-! ## `volume stdCarrier = 1/2`, fully closed

The coordinate characterization of `stdCarrier`'s membership, the analogous characterization of
its mirror `stdCarrier2`, their exact union with the unit square, disjoint interiors (via the same
separating-affine-functional technique used throughout this session's (C3) work), and finally
measure additivity — matching `Dissection.aedisjoint`'s own "disjoint interiors ⟹ a.e. disjoint"
argument, generalized off `Tri` to any pair of convex compact sets. -/

/-- `pb i`'s own coordinates, as a standard basis vector. -/
theorem pb_apply_self (i j : Fin 2) : (pb i : Plane) j = if j = i then 1 else 0 := by
  rw [← pb_repr, Module.Basis.repr_self]
  simp [Finsupp.single_apply, eq_comm]

/-- **The coordinate characterization of `stdCarrier`**: it's exactly the standard right-triangle
region. ⊇ via an explicit barycentric combination (`x = x0•pb0+x1•pb1`, plus a zero weight on `0`);
⊆ via convexity of the halfplane intersection directly (avoiding the need to wrap `stdCarrier` as a
genuine `Tri` — which would need `AffineIndependent ℝ ![0, pb 0, pb 1]` — to reuse
`Tri.carrier_eq_nonneg_coord`). -/
theorem mem_stdCarrier_iff (x : Plane) :
    x ∈ stdCarrier ↔ 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1 := by
  constructor
  · intro hx
    have hlin0 : IsLinearMap ℝ (fun y : Plane => y 0) := ⟨fun a b => rfl, fun c a => rfl⟩
    have hlin1 : IsLinearMap ℝ (fun y : Plane => y 1) := ⟨fun a b => rfl, fun c a => rfl⟩
    have hlinsum : IsLinearMap ℝ (fun y : Plane => y 0 + y 1) :=
      ⟨fun a b => by show a 0 + b 0 + (a 1 + b 1) = a 0 + a 1 + (b 0 + b 1); ring,
       fun c a => by show c * a 0 + c * a 1 = c * (a 0 + a 1); ring⟩
    have hconv : Convex ℝ {y : Plane | 0 ≤ y 0 ∧ 0 ≤ y 1 ∧ y 0 + y 1 ≤ 1} := by
      have h0 : Convex ℝ {y : Plane | 0 ≤ y 0} := convex_halfSpace_ge hlin0 0
      have h1 : Convex ℝ {y : Plane | 0 ≤ y 1} := convex_halfSpace_ge hlin1 0
      have h2 : Convex ℝ {y : Plane | y 0 + y 1 ≤ 1} := convex_halfSpace_le hlinsum 1
      have := (h0.inter h1).inter h2
      convert this using 1
      ext y; simp [and_assoc]
    have hmem : (0:Plane) ∈ {y : Plane | 0 ≤ y 0 ∧ 0 ≤ y 1 ∧ y 0 + y 1 ≤ 1} ∧
        (pb 0 : Plane) ∈ {y : Plane | 0 ≤ y 0 ∧ 0 ≤ y 1 ∧ y 0 + y 1 ≤ 1} ∧
        (pb 1 : Plane) ∈ {y : Plane | 0 ≤ y 0 ∧ 0 ≤ y 1 ∧ y 0 + y 1 ≤ 1} := by
      refine ⟨?_, ?_, ?_⟩ <;> simp [pb_apply_self]
    have hsub : stdCarrier ⊆ {y : Plane | 0 ≤ y 0 ∧ 0 ≤ y 1 ∧ y 0 + y 1 ≤ 1} := by
      apply convexHull_min _ hconv
      rintro y ⟨i, rfl⟩
      fin_cases i
      · exact hmem.1
      · exact hmem.2.1
      · exact hmem.2.2
    exact hsub hx
  · rintro ⟨h0, h1, h2⟩
    refine mem_convexHull_of_exists_fintype (ι := Fin 3)
      ![1 - x 0 - x 1, x 0, x 1] ![(0:Plane), pb 0, pb 1]
      ?_ ?_ ?_ ?_
    · intro i; fin_cases i <;> simp_all <;> linarith
    · rw [Fin.sum_univ_three]
      show 1 - x 0 - x 1 + x 0 + x 1 = 1
      ring
    · intro i; fin_cases i <;> simp
    · rw [Fin.sum_univ_three]
      show (1 - x 0 - x 1) • (0:Plane) + x 0 • pb 0 + x 1 • pb 1 = x
      have hxrepr : x = x 0 • pb 0 + x 1 • pb 1 := by
        conv_lhs => rw [← pb.sum_repr x]
        rw [Fin.sum_univ_two]
        simp [pb_repr]
      conv_rhs => rw [hxrepr]
      module

/-- The reference unit square, living natively in `Plane`. -/
noncomputable def stdSquare : Set Plane :=
  {x : Plane | x 0 ∈ Set.Icc (0:ℝ) 1 ∧ x 1 ∈ Set.Icc (0:ℝ) 1}

theorem stdSquare_eq_preimage :
    stdSquare = (WithLp.ofLp : Plane → (Fin 2 → ℝ)) ⁻¹' (Set.Icc (0 : Fin 2 → ℝ) 1) := by
  ext x
  simp only [stdSquare, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Icc, Pi.le_def, Pi.zero_apply,
    Pi.one_apply]
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;> simp_all
  · rintro ⟨h0, h1⟩
    exact ⟨⟨h0 0, h1 0⟩, ⟨h0 1, h1 1⟩⟩

/-- **`stdSquare` has volume 1.** -/
theorem volume_stdSquare : volume stdSquare = 1 := by
  rw [stdSquare_eq_preimage, (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage]
  · rw [Real.volume_Icc_pi]; simp
  · exact measurableSet_Icc.nullMeasurableSet

/-- **The coordinate characterization of `stdCarrier2`**, via `mem_stdCarrier_iff` transported
through the reflection. -/
theorem mem_stdCarrier2_iff (x : Plane) :
    x ∈ stdCarrier2 ↔ x 0 ≤ 1 ∧ x 1 ≤ 1 ∧ 1 ≤ x 0 + x 1 := by
  have hrefl : x ∈ stdCarrier2 ↔ reflMap x ∈ stdCarrier := by
    constructor
    · intro hx
      rw [stdCarrier2, ← reflMap_stdCarrier] at hx
      obtain ⟨y, hy, hxy⟩ := hx
      have heq : reflMap (reflMap y) = reflMap x := by rw [hxy]
      have hinv : reflMap (reflMap y) = y := by show reflC - (reflC - y) = y; abel
      rw [hinv] at heq
      rw [← heq]; exact hy
    · intro hx
      rw [stdCarrier2, ← reflMap_stdCarrier]
      refine ⟨reflMap x, hx, ?_⟩
      show reflC - (reflC - x) = x
      abel
  rw [hrefl, mem_stdCarrier_iff]
  have h0 : (reflMap x) 0 = reflC 0 - x 0 := rfl
  have h1 : (reflMap x) 1 = reflC 1 - x 1 := rfl
  rw [h0, h1]
  have hc0 : (reflC : Plane) 0 = 1 := by show (pb 0 + pb 1 : Plane) 0 = 1; simp [pb_apply_self]
  have hc1 : (reflC : Plane) 1 = 1 := by show (pb 0 + pb 1 : Plane) 1 = 1; simp [pb_apply_self]
  rw [hc0, hc1]
  constructor
  · rintro ⟨p0, p1, p2⟩; exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨p0, p1, p2⟩; exact ⟨by linarith, by linarith, by linarith⟩

/-- **`stdCarrier` and its mirror exactly tile the unit square.** -/
theorem stdCarrier_union_stdCarrier2 : stdCarrier ∪ stdCarrier2 = stdSquare := by
  ext x
  simp only [Set.mem_union, mem_stdCarrier_iff, mem_stdCarrier2_iff, stdSquare, Set.mem_setOf_eq,
    Set.mem_Icc]
  constructor
  · rintro (⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩)
    · exact ⟨⟨h0, by linarith⟩, ⟨h1, by linarith⟩⟩
    · exact ⟨⟨by linarith, h0⟩, ⟨by linarith, h1⟩⟩
  · rintro ⟨⟨h00, h01⟩, ⟨h10, h11⟩⟩
    rcases le_total (x 0 + x 1) 1 with h | h
    · exact Or.inl ⟨h00, h10, h⟩
    · exact Or.inr ⟨h01, h11, by linarith⟩

/-- **`stdCarrier` and its mirror have disjoint interiors**, separated by the line `x0+x1=1` —
same separating-affine-functional argument as `CertGeom.interiors_disjoint_of_separating`, inlined
here since these sets are raw `Set Plane`s rather than `Tri.carrier`s. -/
theorem interior_stdCarrier_disjoint :
    Disjoint (interior stdCarrier) (interior stdCarrier2) := by
  have hf : IsLinearMap ℝ (fun y : Plane => y 0 + y 1) :=
    ⟨fun a b => by show a 0 + b 0 + (a 1 + b 1) = a 0 + a 1 + (b 0 + b 1); ring,
     fun c a => by show c * a 0 + c * a 1 = c * (a 0 + a 1); ring⟩
  set fl : Plane →ₗ[ℝ] ℝ := hf.mk' with hfldef
  set f : Plane →ᵃ[ℝ] ℝ := fl.toAffineMap with hfdef
  have hflin : f.linear ≠ 0 := by
    intro h
    have h' : fl = (0 : Plane →ₗ[ℝ] ℝ) := h
    have hh : (fl (pb 0) : ℝ) = 0 := by rw [h']; rfl
    rw [show (fl (pb 0) : ℝ) = (pb 0 : Plane) 0 + (pb 0 : Plane) 1 from rfl] at hh
    simp [pb_apply_self] at hh
  have h1 : ∀ x ∈ stdCarrier, f x ≤ 1 := by
    intro x hx; rw [mem_stdCarrier_iff] at hx; exact hx.2.2
  have h2 : ∀ x ∈ stdCarrier2, 1 ≤ f x := by
    intro x hx; rw [mem_stdCarrier2_iff] at hx; exact hx.2.2
  rw [Set.disjoint_left]
  intro x hx1 hx2
  have hxt : x ∈ stdCarrier := interior_subset hx1
  have hxu : x ∈ stdCarrier2 := interior_subset hx2
  have hxc : f x = 1 := le_antisymm (h1 x hxt) (h2 x hxu)
  set g : Plane →ᵃ[ℝ] ℝ := AffineMap.const ℝ Plane 1 - f with hg
  have hglin : g.linear ≠ 0 := by
    intro hcon
    apply hflin
    have hz : (AffineMap.const ℝ Plane (1:ℝ)).linear - f.linear = 0 := hcon
    have hzero : (AffineMap.const ℝ Plane (1:ℝ)).linear = 0 := rfl
    rw [hzero, zero_sub, neg_eq_zero] at hz
    exact hz
  have hgx : g x = 0 := by simp [hg, hxc]
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx1)
  obtain ⟨y, hy, hyneg⟩ := Erdos634.Geometry.exists_neg_near_of_affine_zero g hglin hgx hr
  have hyt : y ∈ stdCarrier := hball hy
  have hcy : 1 < f y := by
    have hgy : g y = 1 - f y := rfl
    rw [hgy] at hyneg
    linarith
  exact absurd (h1 y hyt) (not_le.mpr hcy)

theorem volume_frontier_stdCarrier : volume (frontier stdCarrier) = 0 :=
  (convex_convexHull ℝ _ : Convex ℝ stdCarrier).addHaar_frontier volume

theorem convex_stdCarrier2 : Convex ℝ stdCarrier2 := convex_convexHull ℝ _

theorem volume_frontier_stdCarrier2 : volume (frontier stdCarrier2) = 0 :=
  convex_stdCarrier2.addHaar_frontier volume

theorem isCompact_stdCarrier : IsCompact stdCarrier :=
  (Set.finite_range _).isCompact_convexHull ℝ

theorem isCompact_stdCarrier2 : IsCompact stdCarrier2 :=
  (Set.finite_range _).isCompact_convexHull ℝ

/-- **Disjoint interiors ⟹ a.e. disjoint** — the same argument as `Dissection.aedisjoint`, off
`Tri` since these are raw convex compact sets. -/
theorem aedisjoint_stdCarrier : AEDisjoint volume stdCarrier stdCarrier2 := by
  have hsub : stdCarrier ∩ stdCarrier2 ⊆ frontier stdCarrier ∪ frontier stdCarrier2 := by
    rintro x ⟨hx1, hx2⟩
    by_cases h1 : x ∈ interior stdCarrier
    · by_cases h2 : x ∈ interior stdCarrier2
      · exact absurd h2 (Set.disjoint_left.mp interior_stdCarrier_disjoint h1)
      · exact Or.inr ⟨subset_closure hx2, h2⟩
    · exact Or.inl ⟨subset_closure hx1, h1⟩
  refine measure_mono_null hsub ?_
  exact measure_union_null volume_frontier_stdCarrier volume_frontier_stdCarrier2

/-- **`volume stdCarrier = 1/2`**: `stdCarrier` and its mirror `stdCarrier2` exactly tile the unit
square (`stdCarrier_union_stdCarrier2`), have disjoint interiors hence are a.e. disjoint
(`aedisjoint_stdCarrier`), and have equal volume (`volume_stdCarrier2_eq`) — so each is exactly
half the square's volume `1` (`volume_stdSquare`). This is the missing numeric fact
`area_identity_of_det` never needed (its reference measure always cancels in a ratio), needed here
because `PgramTiling22Bridge`'s target uses `stdSquare`, a different reference set, as its own
normalization. -/
theorem volume_stdCarrier_half : volume stdCarrier = 1 / 2 := by
  have hunion : volume (stdCarrier ∪ stdCarrier2) = volume stdCarrier + volume stdCarrier2 :=
    measure_union₀ isCompact_stdCarrier2.measurableSet.nullMeasurableSet aedisjoint_stdCarrier
  rw [stdCarrier_union_stdCarrier2, volume_stdSquare, volume_stdCarrier2_eq] at hunion
  have h2 : volume stdCarrier + volume stdCarrier = 1 := by rw [← hunion]
  rw [ENNReal.eq_div_iff (by norm_num) (by norm_num)]
  rw [← h2]; ring

end Erdos634.AreaDet
