import Erdos634.CollarDisjointM4

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
