import Erdos634.PgramTiling22
import Erdos634.Z15Real
import Erdos634.CertGeom
import Erdos634.SssCongruent
import Erdos634.ConvexCover
import Erdos634.AreaDet
import Erdos634.Tiling44Bridge

/-!
# `PgramTiling22`, toward a genuine covering statement of the unit parallelogram

Erdős #634. `lem:pgram`/`prop:widecol`'s recorded blocker is "the general parallelogram is a
region with no Lean notion of dissection" — `Dissection`'s `target` field is a `Tri`, so a
parallelogram target cannot literally be packaged as one. But nothing in `ConvexCover`'s actual
*proof* is triangle-specific: `Tri.isCompact`, `.nullMeasurableSet`, `.volume_frontier`,
`.interior_nonempty` all come from generic facts (`Set.finite_range`, `Convex.addHaar_frontier`,
`Convex.interior_nonempty_iff_affineSpan_eq_top`) that hold for the convex hull of *any* finite
point set with full affine span — not just three points. This file builds that generic base for
the specific unit-parallelogram target `(q1,q2,q3,q4)`, as a first step toward a real covering
statement (not yet a `Dissection`, since that type doesn't fit a 4-gon target — the eventual
statement will be a bespoke pointwise-covering `Prop`, built the same way `ConvexCover` was).

**Not a paper-row flip**: this is the target-region groundwork only. The covering statement
itself, the per-piece (C1)-(C4) transfer, and the containment test (needs a diagonal split into
two triangles, since `CertCoord.mem_carrier_of_dets` is a 3-vertex barycentric test) are not done.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.PgramTiling22Bridge

open Erdos634.Z15Real Erdos634.Geometry

def toZPt (p : PgramTiling22.Pt) : ZPt := p

/-- The parallelogram's four real vertices. -/
noncomputable def v1 : Plane := Erdos634.CertCoord.mkPt (toR (zx (toZPt PgramTiling22.q1)))
  (toR (zy (toZPt PgramTiling22.q1)))
noncomputable def v2 : Plane := Erdos634.CertCoord.mkPt (toR (zx (toZPt PgramTiling22.q2)))
  (toR (zy (toZPt PgramTiling22.q2)))
noncomputable def v3 : Plane := Erdos634.CertCoord.mkPt (toR (zx (toZPt PgramTiling22.q3)))
  (toR (zy (toZPt PgramTiling22.q3)))
noncomputable def v4 : Plane := Erdos634.CertCoord.mkPt (toR (zx (toZPt PgramTiling22.q4)))
  (toR (zy (toZPt PgramTiling22.q4)))

/-- The parallelogram, as the convex hull of its four vertices. -/
noncomputable def carrier : Set Plane := convexHull ℝ {v1, v2, v3, v4}

/-- **The parallelogram property**: `v3 = v2 + v4 - v1` (opposite vertices, so the diagonals
bisect each other) — checked componentwise in `ℤ[√15]` by `decide`, transferred by `toR`'s
additivity. This is what makes the affine-parametrization route to (C2) containment work: a
general quadrilateral has no clean closed-form membership test, but a parallelogram is exactly the
affine image of the unit square. -/
theorem v3_eq : v3 = v2 + v4 - v1 := by
  simp only [v1, v2, v3, v4, Erdos634.CertCoord.mkPt]
  have hx : zx (toZPt PgramTiling22.q3)
      = zsub (zadd (zx (toZPt PgramTiling22.q2)) (zx (toZPt PgramTiling22.q4)))
          (zx (toZPt PgramTiling22.q1)) := by decide
  have hy : zy (toZPt PgramTiling22.q3)
      = zsub (zadd (zy (toZPt PgramTiling22.q2)) (zy (toZPt PgramTiling22.q4)))
          (zy (toZPt PgramTiling22.q1)) := by decide
  ext i
  fin_cases i <;> simp <;>
    first
    | (rw [show toR (zx (toZPt PgramTiling22.q3)) = _ from congrArg toR hx, toR_sub, toR_add])
    | (rw [show toR (zy (toZPt PgramTiling22.q3)) = _ from congrArg toR hy, toR_sub, toR_add])

/-- **The affine parametrization of the parallelogram**: `(u,v) ↦ v1 + u•(v2-v1) + v•(v4-v1)`. -/
noncomputable def paramMap : (ℝ × ℝ) →ᵃ[ℝ] Plane where
  toFun p := v1 + p.1 • (v2 - v1) + p.2 • (v4 - v1)
  linear :=
    { toFun := fun p => p.1 • (v2 - v1) + p.2 • (v4 - v1)
      map_add' := by intro x y; simp; module
      map_smul' := by intro c x; simp; module }
  map_vadd' := by intro p q; simp [vadd_eq_add]; module

theorem paramMap_00 : paramMap (0, 0) = v1 := by simp [paramMap]
theorem paramMap_10 : paramMap (1, 0) = v2 := by simp [paramMap]
theorem paramMap_01 : paramMap (0, 1) = v4 := by simp [paramMap]
theorem paramMap_11 : paramMap (1, 1) = v3 := by simp [paramMap, v3_eq]; module

/-- `paramMap` sends the unit square's four corners to the parallelogram's four vertices. -/
theorem corners_eq : paramMap '' (({(0:ℝ), 1} : Set ℝ) ×ˢ ({(0:ℝ), 1} : Set ℝ)) = {v1, v2, v3, v4} := by
  ext p
  simp only [Set.mem_image, Set.mem_prod, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨(rfl | rfl), (rfl | rfl)⟩, rfl⟩
    · left; exact paramMap_00
    · right; right; right; exact paramMap_01
    · right; left; exact paramMap_10
    · right; right; left; exact paramMap_11
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨(0, 0), ⟨Or.inl rfl, Or.inl rfl⟩, paramMap_00⟩
    · exact ⟨(1, 0), ⟨Or.inr rfl, Or.inl rfl⟩, paramMap_10⟩
    · exact ⟨(1, 1), ⟨Or.inr rfl, Or.inr rfl⟩, paramMap_11⟩
    · exact ⟨(0, 1), ⟨Or.inl rfl, Or.inr rfl⟩, paramMap_01⟩

/-- **The parallelogram is exactly the affine image of the unit square.** This is what solves
(C2) containment: a point lies in `carrier` iff its `paramMap`-preimage has both coordinates in
`[0,1]`, which the certificate's four half-plane checks should transfer to directly (not yet
done, but this is the geometric fact those checks encode). -/
theorem carrier_eq_image :
    carrier = paramMap '' ((Set.Icc (0:ℝ) 1) ×ˢ (Set.Icc (0:ℝ) 1)) := by
  rw [show (Set.Icc (0:ℝ) 1) ×ˢ (Set.Icc (0:ℝ) 1) =
      convexHull ℝ (({(0:ℝ), 1} : Set ℝ) ×ˢ ({(0:ℝ), 1} : Set ℝ)) from by
    rw [convexHull_prod, convexHull_pair, segment_eq_Icc (by norm_num : (0:ℝ) ≤ 1)],
    AffineMap.image_convexHull, corners_eq]
  rfl

theorem convex : Convex ℝ carrier := convex_convexHull ℝ _

theorem isCompact : IsCompact carrier :=
  (Set.toFinite ({v1, v2, v3, v4} : Set Plane)).isCompact_convexHull ℝ

theorem measurableSet : MeasurableSet carrier := isCompact.measurableSet

theorem nullMeasurableSet : MeasureTheory.NullMeasurableSet carrier MeasureTheory.volume :=
  measurableSet.nullMeasurableSet

theorem volume_frontier : MeasureTheory.volume (frontier carrier) = 0 :=
  convex.addHaar_frontier MeasureTheory.volume

/-- **Non-degeneracy**: `q1, q2, q3` are affinely independent (a nonzero determinant, `decide`d in
`ℤ[√15]` the same way a triangle's is), so their affine span is already the whole plane. -/
theorem affineIndependent_123 :
    AffineIndependent ℝ (![v1, v2, v3] : Fin 3 → Plane) := by
  apply (affineIndependent_iff_not_collinear_of_ne
    (show (0 : Fin 3) ≠ 1 by decide) (show (0 : Fin 3) ≠ 2 by decide)
    (show (1 : Fin 3) ≠ 2 by decide)).mpr
  apply Erdos634.CertCoord.not_collinear_of_det
  show Erdos634.CertCoord.det3 (toR (zx (toZPt PgramTiling22.q1))) (toR (zy (toZPt PgramTiling22.q1)))
    (toR (zx (toZPt PgramTiling22.q2))) (toR (zy (toZPt PgramTiling22.q2)))
    (toR (zx (toZPt PgramTiling22.q3))) (toR (zy (toZPt PgramTiling22.q3))) ≠ 0
  rw [show Erdos634.CertCoord.det3 (toR (zx (toZPt PgramTiling22.q1))) (toR (zy (toZPt PgramTiling22.q1)))
      (toR (zx (toZPt PgramTiling22.q2))) (toR (zy (toZPt PgramTiling22.q2)))
      (toR (zx (toZPt PgramTiling22.q3))) (toR (zy (toZPt PgramTiling22.q3)))
    = toR (zcross (toZPt PgramTiling22.q1) (toZPt PgramTiling22.q2) (toZPt PgramTiling22.q3))
    from toR_zcross _ _ _]
  exact toR_ne_zero_of_sq_ne (by decide)

/-- **The affine span of the parallelogram's carrier is the whole plane** — via three of its four
vertices being affinely independent, so their span already fills `Plane`. -/
theorem affineSpan_eq_top : affineSpan ℝ carrier = ⊤ := by
  have h : affineSpan ℝ carrier = affineSpan ℝ ({v1, v2, v3, v4} : Set Plane) :=
    affineSpan_convexHull _
  rw [h]
  have h3 : affineSpan ℝ (Set.range (![v1, v2, v3] : Fin 3 → Plane)) = ⊤ :=
    affineIndependent_123.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp)
  refine top_unique ?_
  rw [← h3]
  apply affineSpan_mono
  intro x hx
  simp only [Set.mem_range] at hx
  obtain ⟨i, rfl⟩ := hx
  fin_cases i <;> simp

theorem interior_nonempty : (interior carrier).Nonempty :=
  convex.interior_nonempty_iff_affineSpan_eq_top.mpr affineSpan_eq_top

theorem volume_ne_top : MeasureTheory.volume carrier ≠ ⊤ := isCompact.measure_lt_top.ne

open MeasureTheory

/-- **The covering theorem for the parallelogram target**, the same measure argument as
`ConvexCover.covers_of_volume`, none of which was actually triangle-specific: containment,
pairwise-disjoint interiors and the exact area identity force the pieces to cover the whole
parallelogram, not just sit inside it. -/
theorem covers_of_volume {N : ℕ} (tile : Fin N → Tri)
    (hsub : ∀ i, (tile i).carrier ⊆ carrier)
    (hdisj : Pairwise fun i j => Disjoint (interior (tile i).carrier) (interior (tile j).carrier))
    (hvol : ∑ i, volume (tile i).carrier = volume carrier) :
    (⋃ i, (tile i).carrier) = carrier := by
  classical
  set U : Set Plane := ⋃ i, (tile i).carrier with hUdef
  have hUsub : U ⊆ carrier := Set.iUnion_subset hsub
  have hUvol : volume U = volume carrier := by
    rw [hUdef, Erdos634.ConvexCover.volume_iUnion_eq_sum tile hdisj, hvol]
  have hUclosed : IsClosed U := by
    rw [hUdef]; exact isClosed_iUnion_of_finite fun i => (tile i).isCompact.isClosed
  refine Set.Subset.antisymm hUsub ?_
  by_contra hcon
  obtain ⟨x, hxT, hxU⟩ : ∃ x, x ∈ carrier ∧ x ∉ U := by
    by_contra hall; push_neg at hall; exact hcon fun x hx => hall x hx
  have hVopen : IsOpen (Uᶜ) := hUclosed.isOpen_compl
  have hxcl : x ∈ closure (interior carrier) := by
    have hclosed : IsClosed carrier := isCompact.isClosed
    have := convex.closure_interior_eq_closure_of_nonempty_interior interior_nonempty
    rw [this, hclosed.closure_eq]; exact hxT
  obtain ⟨y, hyV, hyI⟩ : ∃ y, y ∈ Uᶜ ∧ y ∈ interior carrier :=
    mem_closure_iff.mp hxcl (Uᶜ) hVopen hxU
  set W : Set Plane := Uᶜ ∩ interior carrier with hWdef
  have hWopen : IsOpen W := hVopen.inter isOpen_interior
  have hWne : W.Nonempty := ⟨y, hyV, hyI⟩
  have hWpos : 0 < volume W := hWopen.measure_pos volume hWne
  have hWsub : W ⊆ carrier := fun z hz => interior_subset hz.2
  have hWdisj : Disjoint U W := Set.disjoint_right.mpr fun z hz => hz.1
  have hsum : volume U + volume W ≤ volume carrier := by
    have hunion : volume (U ∪ W) = volume U + volume W :=
      measure_union₀ hWopen.measurableSet.nullMeasurableSet hWdisj.aedisjoint
    rw [← hunion]; exact measure_mono (Set.union_subset hUsub hWsub)
  rw [hUvol] at hsum
  have : volume carrier + 0 < volume carrier + volume W :=
    ENNReal.add_lt_add_left volume_ne_top hWpos
  simp only [add_zero] at this
  exact absurd hsum (not_le.mpr this)

/-! ## `paramMap` invertibility: the explicit inverse via Cramer's rule

`carrier_eq_image` says `carrier` is the image of the unit square under `paramMap`. To turn that
into a membership test (`mem_carrier_iff`) we need `paramMap` invertible on its domain; since it is
affine with linear part given by the matrix `[[d2x, d4x], [d2y, d4y]]`, the inverse is the standard
Cramer's-rule formula, and the matrix is nonsingular because `q1, q2, q4` are non-collinear (the
same determinant fact used for `affineIndependent_123`). -/

noncomputable def d2x : ℝ := v2 0 - v1 0
noncomputable def d2y : ℝ := v2 1 - v1 1
noncomputable def d4x : ℝ := v4 0 - v1 0
noncomputable def d4y : ℝ := v4 1 - v1 1
noncomputable def Ddet : ℝ := d2x * d4y - d4x * d2y

theorem Ddet_ne_zero : Ddet ≠ 0 := by
  show d2x * d4y - d4x * d2y ≠ 0
  have : Erdos634.CertCoord.det3 (v1 0) (v1 1) (v2 0) (v2 1) (v4 0) (v4 1) ≠ 0 := by
    show Erdos634.CertCoord.det3 (toR (zx (toZPt PgramTiling22.q1))) (toR (zy (toZPt PgramTiling22.q1)))
      (toR (zx (toZPt PgramTiling22.q2))) (toR (zy (toZPt PgramTiling22.q2)))
      (toR (zx (toZPt PgramTiling22.q4))) (toR (zy (toZPt PgramTiling22.q4))) ≠ 0
    rw [show Erdos634.CertCoord.det3 (toR (zx (toZPt PgramTiling22.q1))) (toR (zy (toZPt PgramTiling22.q1)))
        (toR (zx (toZPt PgramTiling22.q2))) (toR (zy (toZPt PgramTiling22.q2)))
        (toR (zx (toZPt PgramTiling22.q4))) (toR (zy (toZPt PgramTiling22.q4)))
      = toR (zcross (toZPt PgramTiling22.q1) (toZPt PgramTiling22.q2) (toZPt PgramTiling22.q4))
      from toR_zcross _ _ _]
    exact toR_ne_zero_of_sq_ne (by decide)
  simp only [Erdos634.CertCoord.det3, d2x, d2y, d4x, d4y] at *
  convert this using 1

noncomputable def uOf (p : Plane) : ℝ := ((p 0 - v1 0) * d4y - d4x * (p 1 - v1 1)) / Ddet
noncomputable def vOf (p : Plane) : ℝ := (d2x * (p 1 - v1 1) - (p 0 - v1 0) * d2y) / Ddet

theorem paramMap_uOf_vOf (p : Plane) : paramMap (uOf p, vOf p) = p := by
  have hD := Ddet_ne_zero
  have h0 : (paramMap (uOf p, vOf p)) 0 = p 0 := by
    show v1 0 + uOf p * (v2 0 - v1 0) + vOf p * (v4 0 - v1 0) = p 0
    simp only [uOf, vOf]
    field_simp
    simp only [Ddet, d2x, d2y, d4x, d4y]
    ring
  have h1 : (paramMap (uOf p, vOf p)) 1 = p 1 := by
    show v1 1 + uOf p * (v2 1 - v1 1) + vOf p * (v4 1 - v1 1) = p 1
    simp only [uOf, vOf]
    field_simp
    simp only [Ddet, d2x, d2y, d4x, d4y]
    ring
  ext i
  fin_cases i
  · exact h0
  · exact h1

theorem paramMap_unique (u v : ℝ) (p : Plane) (hp : paramMap (u, v) = p) :
    u = uOf p ∧ v = vOf p := by
  have hD := Ddet_ne_zero
  have e0 : (paramMap (u, v)) 0 = p 0 := by rw [hp]
  have e1 : (paramMap (u, v)) 1 = p 1 := by rw [hp]
  have e0' : v1 0 + u * (v2 0 - v1 0) + v * (v4 0 - v1 0) = p 0 := e0
  have e1' : v1 1 + u * (v2 1 - v1 1) + v * (v4 1 - v1 1) = p 1 := e1
  constructor
  · show u = ((p 0 - v1 0) * d4y - d4x * (p 1 - v1 1)) / Ddet
    rw [eq_div_iff hD]
    simp only [Ddet, d2x, d2y, d4x, d4y]
    linear_combination (v4 1 - v1 1) * e0' - (v4 0 - v1 0) * e1'
  · show v = (d2x * (p 1 - v1 1) - (p 0 - v1 0) * d2y) / Ddet
    rw [eq_div_iff hD]
    simp only [Ddet, d2x, d2y, d4x, d4y]
    linear_combination (v2 0 - v1 0) * e1' - (v2 1 - v1 1) * e0'

/-- Membership test for `carrier`: `p` is in the parallelogram iff its `paramMap`-preimage
coordinates both lie in `[0,1]`. -/
theorem mem_carrier_iff (p : Plane) :
    p ∈ carrier ↔ 0 ≤ uOf p ∧ uOf p ≤ 1 ∧ 0 ≤ vOf p ∧ vOf p ≤ 1 := by
  rw [carrier_eq_image]
  constructor
  · rintro ⟨⟨u,v⟩, ⟨hu,hv⟩, hp⟩
    obtain ⟨hu', hv'⟩ := paramMap_unique u v p hp
    exact ⟨hu' ▸ hu.1, hu' ▸ hu.2, hv' ▸ hv.1, hv' ▸ hv.2⟩
  · rintro ⟨h1,h2,h3,h4⟩
    exact ⟨(uOf p, vOf p), ⟨⟨h1,h2⟩,⟨h3,h4⟩⟩, paramMap_uOf_vOf p⟩

/-! ## (C1)/(C2 orientation): the 22 pieces, as real `Tri` objects -/

theorem det3_eq_toR_cross (t : PgramTiling22.Tri) :
    Erdos634.CertCoord.det3
      (toR (zx (toZPt (PgramTiling22.t1 t)))) (toR (zy (toZPt (PgramTiling22.t1 t))))
      (toR (zx (toZPt (PgramTiling22.t2 t)))) (toR (zy (toZPt (PgramTiling22.t2 t))))
      (toR (zx (toZPt (PgramTiling22.t3 t)))) (toR (zy (toZPt (PgramTiling22.t3 t))))
    = toR (zcross (toZPt (PgramTiling22.t1 t)) (toZPt (PgramTiling22.t2 t))
        (toZPt (PgramTiling22.t3 t))) :=
  toR_zcross _ _ _

set_option maxRecDepth 2000 in
theorem all_pieces_pos :
    ∀ t ∈ PgramTiling22.tiles,
      zpos (zcross (toZPt (PgramTiling22.t1 t)) (toZPt (PgramTiling22.t2 t))
        (toZPt (PgramTiling22.t3 t))) = true := by
  decide

noncomputable def pieceTri {t : PgramTiling22.Tri} (ht : t ∈ PgramTiling22.tiles) : Tri :=
  Erdos634.CertCoord.mkTri
    (toR (zx (toZPt (PgramTiling22.t1 t)))) (toR (zy (toZPt (PgramTiling22.t1 t))))
    (toR (zx (toZPt (PgramTiling22.t2 t)))) (toR (zy (toZPt (PgramTiling22.t2 t))))
    (toR (zx (toZPt (PgramTiling22.t3 t)))) (toR (zy (toZPt (PgramTiling22.t3 t))))
    (by rw [det3_eq_toR_cross]; exact (toR_pos (all_pieces_pos t ht)).ne')

theorem dist2_eq_zdist2 (p q : PgramTiling22.Pt) :
    PgramTiling22.dist2 p q = zdist2 (toZPt p) (toZPt q) := rfl

/-- **A piece's vertex, named by index.** -/
def vertexOf (t : PgramTiling22.Tri) (i : Fin 3) : PgramTiling22.Pt :=
  ![PgramTiling22.t1 t, PgramTiling22.t2 t, PgramTiling22.t3 t] i

theorem pieceTri_pts (t : PgramTiling22.Tri) (ht : t ∈ PgramTiling22.tiles) (i : Fin 3) :
    (pieceTri ht).pts i
      = Erdos634.CertCoord.mkPt (toR (zx (toZPt (vertexOf t i)))) (toR (zy (toZPt (vertexOf t i)))) := by
  fin_cases i <;> rfl

theorem pieceTri_dist_sq (t : PgramTiling22.Tri) (ht : t ∈ PgramTiling22.tiles) (i j : Fin 3) :
    dist ((pieceTri ht).pts i) ((pieceTri ht).pts j) ^ 2
      = toR (PgramTiling22.dist2 (vertexOf t i) (vertexOf t j)) := by
  rw [pieceTri_pts t ht i, pieceTri_pts t ht j, Erdos634.CertCoord.dist_sq_mkPt, dist2_eq_zdist2]
  exact toR_zdist2 _ _

/-! ## (C1): every piece is congruent to a fixed model -/

theorem headI_mem_tiles : PgramTiling22.tiles.headI ∈ PgramTiling22.tiles := by decide

def congOK' (t : PgramTiling22.Tri) : Bool :=
  decide (∃ σ : Equiv.Perm (Fin 3), ∀ i j : Fin 3,
    PgramTiling22.dist2 (vertexOf t i) (vertexOf t j)
      = PgramTiling22.dist2 (vertexOf PgramTiling22.tiles.headI (σ i))
          (vertexOf PgramTiling22.tiles.headI (σ j)))

set_option maxRecDepth 2000 in
theorem all_pieces_cong : ∀ t ∈ PgramTiling22.tiles, congOK' t = true := by decide

theorem pieceTri_congruent {t : PgramTiling22.Tri} (ht : t ∈ PgramTiling22.tiles) :
    (pieceTri ht).Congruent (pieceTri headI_mem_tiles) := by
  have hex := all_pieces_cong t ht
  simp only [congOK', decide_eq_true_eq] at hex
  obtain ⟨σ, hσ⟩ := hex
  refine Erdos634.SssCongruent.congruent_of_sq_dist_perm σ (fun i j => ?_)
  rw [pieceTri_dist_sq t ht, pieceTri_dist_sq PgramTiling22.tiles.headI headI_mem_tiles]
  exact congrArg toR (hσ i j)

end Erdos634.PgramTiling22Bridge
