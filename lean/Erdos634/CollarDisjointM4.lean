import Erdos634.CertCoord
import Erdos634.StraightEdgeSums
import Erdos634.CertGeom
import Erdos634.TranslateDissection
import Erdos634.CollarGeometryM4
import Erdos634.PgramTiling22Bridge
import Erdos634.Realizable

/-!
# The `m=2 → m=4` collar step — first disjointness proof

Erdős #634. `thm:realize12`'s existence half needs `Δ_4` built as one flat `Dissection 176` from
translated copies of `Tiling44Bridge.dissection` and `PgramTiling22`'s pieces
(`private/VERIFY_PLAN.md`'s 2026-09-05 entries; `CollarGeometryM4.lean` confirmed the placement
coordinates). The certificate needs, among other things, that every pair of the `176` pieces has
disjoint interiors — most pairs (pieces from different "regions": the corner triangle, `Δ_2^apex`,
each column) are separated by a straight line between the regions, the same
"separating-affine-functional" argument every certificate in this project already uses
(`CertGeom.interiors_disjoint_of_separating`).

This file proves the first, simplest instance: `Δ_2^apex` (`Tiling44Bridge.dissection` translated
by `(88, 24√15)`) and the corner triangle (`Tiling44Bridge.dissection` translated by `(176, 0)`)
have disjoint interiors — separated by the horizontal line `y = 24√15` (`Δ_2^apex`'s base, the
corner triangle's apex height). `yFun`/`yAff` (the `y`-coordinate as a linear/affine functional on
`Plane`) and `carrier_yAff_ge`/`carrier_yAff_le` (a triangle's carrier lies in a half-plane once its
three vertices do, via `Tri.carrier_subset_halfplane_affine`) are the reusable pieces; the same
pattern applies to every other region-pair in the eventual full certificate.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.CertCoord Erdos634.TranslateDissection Erdos634.CertGeom
open Erdos634.DissectionMap

/-- The `y`-coordinate of a point of the plane, as a linear functional. -/
noncomputable def yFun : Plane →ₗ[ℝ] ℝ where
  toFun p := p 1
  map_add' p q := by simp [PiLp.add_apply]
  map_smul' c p := by simp [PiLp.smul_apply]

theorem yFun_mkPt (x y : ℝ) : yFun (mkPt x y) = y := by
  show mkPt x y 1 = y
  exact mkPt_one x y

theorem yFun_ne_zero : yFun ≠ 0 := by
  intro h
  have h2 : yFun (mkPt 0 1) = 1 := yFun_mkPt 0 1
  rw [h] at h2
  simp at h2

/-- The `y`-coordinate, as an affine functional. -/
noncomputable def yAff : Plane →ᵃ[ℝ] ℝ := yFun.toAffineMap

theorem yAff_linear_ne_zero : yAff.linear ≠ 0 := yFun_ne_zero

theorem yAff_mkPt (x y : ℝ) : yAff (mkPt x y) = y := yFun_mkPt x y

/-- If a triangle's three vertices all satisfy `c ≤ yAff`, so does its whole carrier. -/
theorem carrier_yAff_ge (T : Tri) (c : ℝ) (h : ∀ i, c ≤ yAff (T.pts i)) :
    ∀ y ∈ T.carrier, c ≤ yAff y := by
  have hg : ∀ i, 0 ≤ (yAff - AffineMap.const ℝ Plane c) (T.pts i) := by
    intro i
    show 0 ≤ yAff (T.pts i) - c
    linarith [h i]
  have hsub := Tri.carrier_subset_halfplane_affine T (yAff - AffineMap.const ℝ Plane c) hg
  intro y hy
  have h2 : 0 ≤ yAff y - c := hsub y hy
  linarith

/-- If a triangle's three vertices all satisfy `yAff ≤ c`, so does its whole carrier. -/
theorem carrier_yAff_le (T : Tri) (c : ℝ) (h : ∀ i, yAff (T.pts i) ≤ c) :
    ∀ y ∈ T.carrier, yAff y ≤ c := by
  have hg : ∀ i, 0 ≤ (AffineMap.const ℝ Plane c - yAff) (T.pts i) := by
    intro i
    show 0 ≤ c - yAff (T.pts i)
    linarith [h i]
  have hsub := Tri.carrier_subset_halfplane_affine T (AffineMap.const ℝ Plane c - yAff) hg
  intro y hy
  have h2 : 0 ≤ c - yAff y := hsub y hy
  linarith

/-- **`Δ_2^apex` and the corner triangle have disjoint interiors** — separated by the horizontal
line `y = 24√15`. The first real disjointness proof toward `Δ_4`'s full certificate. -/
theorem apex_corner_disjoint :
    Disjoint (interior (translateCongruentDissection (mkPt 88 (24 * Real.sqrt 15))
        Erdos634.Tiling44Bridge.dissection).target.carrier)
      (interior (translateCongruentDissection (mkPt 176 0)
        Erdos634.Tiling44Bridge.dissection).target.carrier) := by
  refine (interiors_disjoint_of_separating yAff yAff_linear_ne_zero (24 * Real.sqrt 15) ?_ ?_).symm
  · -- corner triangle: yAff ≤ c
    apply carrier_yAff_le _ (24 * Real.sqrt 15)
    intro i
    fin_cases i
    · show yAff ((translateCongruentDissection (mkPt 176 0)
          Erdos634.Tiling44Bridge.dissection).target.pts 0) ≤ _
      rw [corner_copy_pts.1, yAff_mkPt]; norm_num
    · show yAff ((translateCongruentDissection (mkPt 176 0)
          Erdos634.Tiling44Bridge.dissection).target.pts 1) ≤ _
      rw [corner_copy_pts.2.1, yAff_mkPt]; norm_num
    · show yAff ((translateCongruentDissection (mkPt 176 0)
          Erdos634.Tiling44Bridge.dissection).target.pts 2) ≤ _
      rw [corner_copy_pts.2.2, yAff_mkPt]
  · -- apex triangle: c ≤ yAff
    apply carrier_yAff_ge _ (24 * Real.sqrt 15)
    intro i
    fin_cases i
    · show _ ≤ yAff ((translateCongruentDissection (mkPt 88 (24 * Real.sqrt 15))
          Erdos634.Tiling44Bridge.dissection).target.pts 0)
      rw [apex_copy_pts.1, yAff_mkPt]
    · show _ ≤ yAff ((translateCongruentDissection (mkPt 88 (24 * Real.sqrt 15))
          Erdos634.Tiling44Bridge.dissection).target.pts 1)
      rw [apex_copy_pts.2.1, yAff_mkPt]
    · show _ ≤ yAff ((translateCongruentDissection (mkPt 88 (24 * Real.sqrt 15))
          Erdos634.Tiling44Bridge.dissection).target.pts 2)
      rw [apex_copy_pts.2.2, yAff_mkPt]; nlinarith [Real.sqrt_nonneg (15:ℝ)]

/-! ## A uniform `y`-bound for every `PgramTiling22` piece

Every one of `PgramTiling22`'s `22` raw pieces has `y`-coordinates in `[0, 6√15]` (before any
placement rescale/translation) — a single fact, derived once via convexity, that will let the
eventual full certificate show *every* column piece (all four translated/rescaled copies) is
disjoint from `Δ_2^apex` without 88 separate per-piece checks: after `×2` rescale and the column's
own translation, this becomes `y ∈ [0, 24√15]`, matching `apex_corner_disjoint`'s separating line
exactly. -/

theorem v_ycoords :
    yAff Erdos634.PgramTiling22Bridge.v1 = 0 ∧
    yAff Erdos634.PgramTiling22Bridge.v2 = 0 ∧
    yAff Erdos634.PgramTiling22Bridge.v3 = 6 * Real.sqrt 15 ∧
    yAff Erdos634.PgramTiling22Bridge.v4 = 6 * Real.sqrt 15 := by
  have key : ∀ (q : PgramTiling22.Pt) (b : ℤ),
      Erdos634.Z15Real.zy (q : Erdos634.Z15Real.ZPt) = (0, b) →
      yAff (mkPt (Erdos634.Z15Real.toR (Erdos634.Z15Real.zx (q : Erdos634.Z15Real.ZPt)))
          (Erdos634.Z15Real.toR (Erdos634.Z15Real.zy (q : Erdos634.Z15Real.ZPt))))
        = (b:ℝ) * Real.sqrt 15 := by
    intro q b hy
    rw [hy, yAff_mkPt]
    simp only [Erdos634.Z15Real.toR]
    push_cast
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := key PgramTiling22.q1 0 (by decide)
    unfold Erdos634.PgramTiling22Bridge.v1 Erdos634.PgramTiling22Bridge.toZPt
    rw [this]; norm_num
  · have := key PgramTiling22.q2 0 (by decide)
    unfold Erdos634.PgramTiling22Bridge.v2 Erdos634.PgramTiling22Bridge.toZPt
    rw [this]; norm_num
  · have := key PgramTiling22.q3 6 (by decide)
    unfold Erdos634.PgramTiling22Bridge.v3 Erdos634.PgramTiling22Bridge.toZPt
    rw [this]; norm_num
  · have := key PgramTiling22.q4 6 (by decide)
    unfold Erdos634.PgramTiling22Bridge.v4 Erdos634.PgramTiling22Bridge.toZPt
    rw [this]; norm_num

/-- **`PgramTiling22`'s whole carrier has `y`-coordinates in `[0, 6√15]`.** Composes the four
corners' `y`-bounds with `convexHull_min`, since the halfplane bounds are convex. -/
theorem carrier_yBound :
    ∀ p ∈ Erdos634.PgramTiling22Bridge.carrier, 0 ≤ yAff p ∧ yAff p ≤ 6 * Real.sqrt 15 := by
  have hconv : Convex ℝ {p : Plane | 0 ≤ yAff p ∧ yAff p ≤ 6 * Real.sqrt 15} := by
    apply Convex.inter
    · exact (convex_Ici (0:ℝ)).affine_preimage yAff
    · exact (convex_Iic (6 * Real.sqrt 15)).affine_preimage yAff
  have hsub : ({Erdos634.PgramTiling22Bridge.v1, Erdos634.PgramTiling22Bridge.v2,
      Erdos634.PgramTiling22Bridge.v3, Erdos634.PgramTiling22Bridge.v4} : Set Plane)
      ⊆ {p : Plane | 0 ≤ yAff p ∧ yAff p ≤ 6 * Real.sqrt 15} := by
    have h1 := v_ycoords.1
    have h2 := v_ycoords.2.1
    have h3 := v_ycoords.2.2.1
    have h4 := v_ycoords.2.2.2
    have hpos : (0:ℝ) ≤ 6 * Real.sqrt 15 := by positivity
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact ⟨h1.ge, by rw [h1]; exact hpos⟩
    · exact ⟨h2.ge, by rw [h2]; exact hpos⟩
    · exact ⟨by rw [h3]; exact hpos, h3.le⟩
    · exact ⟨by rw [h4]; exact hpos, h4.le⟩
  exact convexHull_min hsub hconv

/-- **Every piece of `PgramTiling22` has `y`-coordinates in `[0, 6√15]`** (before any placement
rescale/translation) — composes `pieceTri_subset_carrier` with `carrier_yBound`. -/
theorem piece_yBound {t : PgramTiling22.Tri} (ht : t ∈ PgramTiling22.tiles) (i : Fin 3) :
    0 ≤ yAff ((Erdos634.PgramTiling22Bridge.pieceTri ht).pts i) ∧
    yAff ((Erdos634.PgramTiling22Bridge.pieceTri ht).pts i) ≤ 6 * Real.sqrt 15 := by
  apply carrier_yBound
  apply Erdos634.PgramTiling22Bridge.pieceTri_subset_carrier ht
  exact subset_convexHull ℝ _ (Set.mem_range_self i)

/-! ## Every column piece is disjoint from `Δ_2^apex` — all 88 pieces at once

A raw `PgramTiling22` piece is placed as a column piece by scaling ×2 about the origin, then
translating: the bottom half of any column by a vector with `y = 0`, the top half by one with
`y = 12√15` (per `private/VERIFY_PLAN.md`'s 2026-09-05 hand-derivation — the specific `x`-shift
varies with the column index, but never affects the `y`-bound). `scaledPiece_yBound` shows this
places every piece's `y`-coordinate in `[0, 24√15]` regardless of which piece or which column, so
one theorem (`column_piece_apex_disjoint`) gives disjointness from `Δ_2^apex` for all `88` column
pieces (`2` columns `× 2` halves `× 22` pieces) at once. -/

theorem yAff_homothety (v p : Plane) (r : ℝ) :
    yAff (AffineMap.homothety v r p) = r * yAff p + (1 - r) * yAff v := by
  rw [AffineMap.homothety_apply, AffineMap.map_vadd, vadd_eq_add]
  have h1 : yAff.linear (r • (p -ᵥ v)) = r * yAff p - r * yAff v := by
    rw [map_smul]
    show r * yFun (p -ᵥ v) = _
    have h2 : yFun (p -ᵥ v) = yAff p - yAff v := by
      show yFun (p - v) = _
      rw [map_sub]
      rfl
    rw [h2]
    ring
  rw [h1]
  ring

theorem yAff_vadd (p w : Plane) : yAff (w +ᵥ p) = yAff w + yAff p := by
  rw [AffineMap.map_vadd, vadd_eq_add]
  rfl

/-- Every raw `PgramTiling22` piece, scaled ×2 about the origin, has `y ∈ [0, 12√15]`. -/
theorem scaledPiece_yBound {t : PgramTiling22.Tri} (ht : t ∈ PgramTiling22.tiles) (i : Fin 3) :
    0 ≤ yAff (Erdos634.Realizable.homothetyEquiv (mkPt 0 0) 2 (by norm_num)
        ((Erdos634.PgramTiling22Bridge.pieceTri ht).pts i)) ∧
    yAff (Erdos634.Realizable.homothetyEquiv (mkPt 0 0) 2 (by norm_num)
        ((Erdos634.PgramTiling22Bridge.pieceTri ht).pts i)) ≤ 12 * Real.sqrt 15 := by
  rw [Erdos634.Realizable.homothetyEquiv_apply, yAff_homothety, yAff_mkPt]
  have hb := piece_yBound ht i
  constructor <;> nlinarith [hb.1, hb.2]

/-- **Every placed column piece is disjoint from `Δ_2^apex`.** A raw `PgramTiling22` piece, scaled
×2 about the origin, then translated by `w` with `y(w) ∈ {0, 12√15}` (the bottom or top half of any
column), has interior disjoint from `Δ_2^apex`'s — covers all `88` column pieces at once. -/
theorem column_piece_apex_disjoint {t : PgramTiling22.Tri} (ht : t ∈ PgramTiling22.tiles)
    (w : Plane) (hw : yAff w = 0 ∨ yAff w = 12 * Real.sqrt 15) :
    Disjoint
      (interior (mapTri (AffineEquiv.constVAdd ℝ Plane w)
        (mapTri (Erdos634.Realizable.homothetyEquiv (mkPt 0 0) 2 (by norm_num))
          (Erdos634.PgramTiling22Bridge.pieceTri ht))).carrier)
      (interior (translateCongruentDissection (mkPt 88 (24 * Real.sqrt 15))
        Erdos634.Tiling44Bridge.dissection).target.carrier) := by
  refine interiors_disjoint_of_separating yAff yAff_linear_ne_zero (24 * Real.sqrt 15) ?_ ?_
  · apply carrier_yAff_le _ (24 * Real.sqrt 15)
    intro i
    show yAff (AffineEquiv.constVAdd ℝ Plane w
      ((Erdos634.Realizable.homothetyEquiv (mkPt 0 0) 2 (by norm_num))
        ((Erdos634.PgramTiling22Bridge.pieceTri ht).pts i))) ≤ _
    show yAff (w +ᵥ Erdos634.Realizable.homothetyEquiv (mkPt 0 0) 2 (by norm_num)
        ((Erdos634.PgramTiling22Bridge.pieceTri ht).pts i)) ≤ _
    rw [yAff_vadd]
    have hb := scaledPiece_yBound ht i
    rcases hw with hw | hw <;> rw [hw] <;> linarith [hb.2]
  · apply carrier_yAff_ge _ (24 * Real.sqrt 15)
    intro i
    fin_cases i
    · show _ ≤ yAff ((translateCongruentDissection (mkPt 88 (24 * Real.sqrt 15))
          Erdos634.Tiling44Bridge.dissection).target.pts 0)
      rw [apex_copy_pts.1, yAff_mkPt]
    · show _ ≤ yAff ((translateCongruentDissection (mkPt 88 (24 * Real.sqrt 15))
          Erdos634.Tiling44Bridge.dissection).target.pts 1)
      rw [apex_copy_pts.2.1, yAff_mkPt]
    · show _ ≤ yAff ((translateCongruentDissection (mkPt 88 (24 * Real.sqrt 15))
          Erdos634.Tiling44Bridge.dissection).target.pts 2)
      rw [apex_copy_pts.2.2, yAff_mkPt]; nlinarith [Real.sqrt_nonneg (15:ℝ)]

/-! ## Within-copy disjointness, transported from the source certificates

`PgramTiling22Bridge.pieces_interiors_disjoint` already proves any two distinct pieces of
`PgramTiling22` are interior-disjoint, unconditionally. `DissectionMap.mapTri_mapTri_interiors_disjoint`
transports that fact through the placement maps (scale ×2 about the origin, then translate) without
re-deriving any separating line — the same technique `mapDissection`'s own `interiors_disjoint`
field already uses, now available as a standalone tool for a placement outside a `Dissection`
wrapper (needed here since `PgramTiling22` itself has no `CongruentDissection` object). -/

/-- **Two distinct pieces of the same placed `PgramTiling22` copy are interior-disjoint.**
Transports `PgramTiling22Bridge.pieces_interiors_disjoint` through the placement maps — no new
separating-line argument needed. -/
theorem placed_pieces_interiors_disjoint {A B : PgramTiling22.Tri}
    (hA : A ∈ PgramTiling22.tiles) (hB : B ∈ PgramTiling22.tiles) (hne : A ≠ B) (w : Plane) :
    Disjoint
      (interior (mapTri (AffineEquiv.constVAdd ℝ Plane w)
        (mapTri (Erdos634.Realizable.homothetyEquiv (mkPt 0 0) 2 (by norm_num))
          (Erdos634.PgramTiling22Bridge.pieceTri hA))).carrier)
      (interior (mapTri (AffineEquiv.constVAdd ℝ Plane w)
        (mapTri (Erdos634.Realizable.homothetyEquiv (mkPt 0 0) 2 (by norm_num))
          (Erdos634.PgramTiling22Bridge.pieceTri hB))).carrier) :=
  mapTri_mapTri_interiors_disjoint _ _
    (Erdos634.PgramTiling22Bridge.pieces_interiors_disjoint hA hB hne)

/-! ## Within-copy disjointness for the two `Tiling44`-based pieces

The same transport pattern as `placed_pieces_interiors_disjoint`, applied to
`Tiling44Bridge.dissection.interiors_disjoint` instead of `PgramTiling22Bridge`'s: covers
within-`Δ_2^apex` and within-corner-triangle disjointness at once, for any translation vector. -/

/-- **Two distinct tiles of a translated copy of `Tiling44Bridge.dissection` are interior-disjoint.**
Transports `Tiling44Bridge.dissection.interiors_disjoint` through the translation — no new
separating-line argument needed. Instantiating `v` at `(88, 24√15)` or `(176, 0)` gives
within-`Δ_2^apex` and within-corner-triangle disjointness respectively. -/
theorem translated_tiling44_interiors_disjoint (v : Plane)
    {i j : Fin Tiling44.tiles.length} (hij : i ≠ j) :
    Disjoint (interior ((translateCongruentDissection v
        Erdos634.Tiling44Bridge.dissection).tile i).carrier)
      (interior ((translateCongruentDissection v
        Erdos634.Tiling44Bridge.dissection).tile j).carrier) := by
  simp only [translateCongruentDissection_tile]
  exact mapTri_interiors_disjoint _ (Erdos634.Tiling44Bridge.dissection.interiors_disjoint hij)
