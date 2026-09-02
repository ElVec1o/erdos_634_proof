import Erdos634.CertCoord
import Erdos634.StraightEdgeSums
import Erdos634.CertGeom
import Erdos634.TranslateDissection
import Erdos634.CollarGeometryM4

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
