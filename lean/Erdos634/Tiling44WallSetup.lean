import Erdos634.CollarDisjointM4
import Erdos634.Tiling44Bridge
import Erdos634.StraightEdgeSums

/-!
# A concrete wall line for `Tiling44Bridge`'s target, and its `hker`

Erdős #634. Continues instantiating `SideWalk.side_walk_of_dissection` for
`Tiling44Bridge.dissection` (toward `lem:ccornerside`). `Tiling44Bridge.dissection.target` has
vertices `(0,0)`, `(176,0)`, `(88,24√15)` (base length `176`, the two equal sides length `128`
each — confirmed by `targetTri_sides`, matching this session's earlier `Δ_2` collar-construction
coordinates). This file picks the concrete `g`/`dir` pair for the equal side from `(176,0)` to the
apex `(88,24√15)`, and discharges `side_walk_of_dissection`'s `hker` hypothesis for that choice.

`gWall(x,y) = 24√15·x + 88·y` is the affine functional whose level set through `(176,0)` and
`(88,24√15)` is exactly this side's line (checked: both points give `4224√15`); its gradient
`(24√15, 88)` is the line's own normal. `dirWall` is the (already-normalized, `/128`) linear
functional along the line's own direction, `(-88, 24√15)/128` — orthogonal to `gWall`'s gradient
by construction (`24√15·(-88) + 88·24√15 = 0`), which is exactly what makes `hker` hold: the two
functionals' gradients form a basis of the plane (their determinant `88² + (24√15)² = 16384 ≠ 0`).

Axiom-clean; no `sorry`.
-/

open Erdos634.CertCoord Erdos634.Geometry

/-- The affine functional (as a linear map on the underlying vector space) whose level set is
`Tiling44Bridge`'s equal side from `(176,0)` to the apex `(88,24√15)`. -/
noncomputable def gWall : Plane →ₗ[ℝ] ℝ := (24 * Real.sqrt 15) • xFun + (88:ℝ) • yFun

/-- The (unit-normalized) direction along that same wall line. -/
noncomputable def dirWall : Plane →ₗ[ℝ] ℝ :=
  ((-88:ℝ)/128) • xFun + (24 * Real.sqrt 15 / 128) • yFun

theorem gWall_mkPt (x y : ℝ) : gWall (mkPt x y) = 24 * Real.sqrt 15 * x + 88 * y := by
  simp only [gWall, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, xFun_mkPt, yFun_mkPt]

theorem dirWall_mkPt (x y : ℝ) : dirWall (mkPt x y) = (-88 * x + 24 * Real.sqrt 15 * y) / 128 := by
  simp only [dirWall, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, xFun_mkPt, yFun_mkPt]
  ring

/-- **`hker` for the `(gWall, dirWall)` pair**: the only vector killed by both is `0`. -/
theorem hker_wall : ∀ v : Plane, gWall v = 0 → dirWall v = 0 → v = 0 := by
  intro v hg hd
  have hv : v = mkPt (xFun v) (yFun v) := by
    ext j; fin_cases j
    · show _ = xFun v; rfl
    · show _ = yFun v; rfl
  rw [hv] at hg hd ⊢
  rw [gWall_mkPt] at hg
  rw [dirWall_mkPt] at hd
  have hd' : -88 * (xFun v) + 24 * Real.sqrt 15 * (yFun v) = 0 := by
    field_simp at hd; linarith [hd]
  have hs : Real.sqrt 15 ^ 2 = 15 := Real.sq_sqrt (by norm_num)
  have hy0 : yFun v = 0 := by
    have key : (88 * 88 + 24 * Real.sqrt 15 * (24 * Real.sqrt 15)) * yFun v = 0 := by
      linear_combination 88 * hg + 24 * Real.sqrt 15 * hd'
    nlinarith [key, hs]
  have hx0 : xFun v = 0 := by nlinarith [hg, hd', hy0]
  rw [hx0, hy0]
  ext j; fin_cases j <;> simp [mkPt]

open Erdos634.Z15Real in
/-- `Tiling44Bridge`'s target vertex `0` is exactly `(0,0)`. -/
theorem tiling44_targetTri_pts0 : Erdos634.Tiling44Bridge.targetTri.pts 0 = mkPt 0 0 := by
  rw [Erdos634.Tiling44Bridge.targetTri_pts_eq]
  show mkPt (toR (zx (Erdos634.Tiling44Bridge.toZPt (Tiling44.t1 Tiling44.target))))
    (toR (zy (Erdos634.Tiling44Bridge.toZPt (Tiling44.t1 Tiling44.target)))) = mkPt 0 0
  have hx : zx (Erdos634.Tiling44Bridge.toZPt (Tiling44.t1 Tiling44.target)) = ((0:ℤ),(0:ℤ)) := by decide
  have hy : zy (Erdos634.Tiling44Bridge.toZPt (Tiling44.t1 Tiling44.target)) = ((0:ℤ),(0:ℤ)) := by decide
  rw [hx, hy]; simp [toR]

open Erdos634.Z15Real in
/-- `Tiling44Bridge`'s target vertex `1` is exactly `(176,0)`. -/
theorem tiling44_targetTri_pts1 : Erdos634.Tiling44Bridge.targetTri.pts 1 = mkPt 176 0 := by
  rw [Erdos634.Tiling44Bridge.targetTri_pts_eq]
  show mkPt (toR (zx (Erdos634.Tiling44Bridge.toZPt (Tiling44.t2 Tiling44.target))))
    (toR (zy (Erdos634.Tiling44Bridge.toZPt (Tiling44.t2 Tiling44.target)))) = mkPt 176 0
  have hx : zx (Erdos634.Tiling44Bridge.toZPt (Tiling44.t2 Tiling44.target)) = ((176:ℤ),(0:ℤ)) := by decide
  have hy : zy (Erdos634.Tiling44Bridge.toZPt (Tiling44.t2 Tiling44.target)) = ((0:ℤ),(0:ℤ)) := by decide
  rw [hx, hy]; simp [toR]

open Erdos634.Z15Real in
/-- `Tiling44Bridge`'s target vertex `2` (the apex) is exactly `(88,24√15)`. -/
theorem tiling44_targetTri_pts2 :
    Erdos634.Tiling44Bridge.targetTri.pts 2 = mkPt 88 (24 * Real.sqrt 15) := by
  rw [Erdos634.Tiling44Bridge.targetTri_pts_eq]
  show mkPt (toR (zx (Erdos634.Tiling44Bridge.toZPt (Tiling44.t3 Tiling44.target))))
    (toR (zy (Erdos634.Tiling44Bridge.toZPt (Tiling44.t3 Tiling44.target)))) = mkPt 88 (24 * Real.sqrt 15)
  have hx : zx (Erdos634.Tiling44Bridge.toZPt (Tiling44.t3 Tiling44.target)) = ((88:ℤ),(0:ℤ)) := by decide
  have hy : zy (Erdos634.Tiling44Bridge.toZPt (Tiling44.t3 Tiling44.target)) = ((0:ℤ),(24:ℤ)) := by decide
  rw [hx, hy]; simp [toR]

noncomputable def gWallAff : Plane →ᵃ[ℝ] ℝ := gWall.toAffineMap

theorem gWallAff_mkPt (x y : ℝ) : gWallAff (mkPt x y) = 24 * Real.sqrt 15 * x + 88 * y :=
  gWall_mkPt x y

/-- **`hwall` for `gWall`**: `Tiling44Bridge`'s target lies entirely on the `gWall ≤ 4224√15`
side, touching the boundary exactly along the wall line's own two named endpoints. -/
theorem hwall_wall :
    ∀ y ∈ Erdos634.Tiling44Bridge.targetTri.carrier, gWallAff y ≤ 4224 * Real.sqrt 15 := by
  have hi : ∀ i, 0 ≤ (AffineMap.const ℝ Plane (4224 * Real.sqrt 15) - gWallAff)
      (Erdos634.Tiling44Bridge.targetTri.pts i) := by
    intro i
    fin_cases i
    · show 0 ≤ 4224 * Real.sqrt 15 - gWallAff (Erdos634.Tiling44Bridge.targetTri.pts 0)
      rw [tiling44_targetTri_pts0, gWallAff_mkPt]
      nlinarith [Real.sqrt_nonneg (15:ℝ)]
    · show 0 ≤ 4224 * Real.sqrt 15 - gWallAff (Erdos634.Tiling44Bridge.targetTri.pts 1)
      rw [tiling44_targetTri_pts1, gWallAff_mkPt]; ring_nf; norm_num
    · show 0 ≤ 4224 * Real.sqrt 15 - gWallAff (Erdos634.Tiling44Bridge.targetTri.pts 2)
      rw [tiling44_targetTri_pts2, gWallAff_mkPt]; ring_nf; norm_num
  intro y hy
  have hsub := Tri.carrier_subset_halfplane_affine Erdos634.Tiling44Bridge.targetTri
    (AffineMap.const ℝ Plane (4224 * Real.sqrt 15) - gWallAff) hi y hy
  have hsub' : 0 ≤ 4224 * Real.sqrt 15 - gWallAff y := hsub
  linarith
