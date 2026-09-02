import Erdos634.CollarDisjointM4
import Erdos634.Tiling44Bridge
import Erdos634.StraightEdgeSums
import Erdos634.SideWall
import Erdos634.SupportFace

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

/-- **`hbase` for `gWall`**: the segment from `(176,0)` to the apex `(88,24√15)` is the equal
side's own edge, hence lies on the target's frontier. -/
theorem hbase_wall :
    segment ℝ (Erdos634.Tiling44Bridge.targetTri.pts 1) (Erdos634.Tiling44Bridge.targetTri.pts 2)
      ⊆ frontier Erdos634.Tiling44Bridge.targetTri.carrier := by
  have := Erdos634.SideWall.edge_subset_frontier Erdos634.Tiling44Bridge.targetTri 1
  rwa [Tri.edge] at this

/-- **`hline` for `gWall`**: `gWall` is exactly `4224√15` on the whole segment, not just at its
endpoints — a direct consequence of `gWall` agreeing with that value at both ends and being
affine. -/
theorem hline_wall :
    ∀ y ∈ segment ℝ (Erdos634.Tiling44Bridge.targetTri.pts 1)
      (Erdos634.Tiling44Bridge.targetTri.pts 2), gWallAff y = 4224 * Real.sqrt 15 := by
  intro y hy
  obtain ⟨u, v, hu, hv, huv, rfl⟩ := hy
  rw [tiling44_targetTri_pts1, tiling44_targetTri_pts2] at *
  have hmk : u • mkPt 176 0 + v • mkPt 88 (24 * Real.sqrt 15)
      = mkPt (176 * u + 88 * v) (24 * Real.sqrt 15 * v) := by
    ext j; fin_cases j
    · show u * (mkPt (176:ℝ) 0) 0 + v * (mkPt (88:ℝ) (24 * Real.sqrt 15)) 0 = _
      simp [mkPt]; ring
    · show u * (mkPt (176:ℝ) 0) 1 + v * (mkPt (88:ℝ) (24 * Real.sqrt 15)) 1 = _
      simp [mkPt]; ring
  rw [hmk, gWallAff_mkPt]
  have : u = 1 - v := by linarith
  rw [this]; ring

/-- **`hface` for `gWall`**: any target point where `gWall` reaches `4224√15` lies on the wall
segment — the target only touches its own supporting line along this one edge. Via
`SupportFace.mem_convexHull_max` (pre-existing, general): a convex-hull point attaining a linear
functional's bound must be a combination of only the vertices that also attain it, and here only
`pts 1` and `pts 2` do (`pts 0` is strictly below, `gWall (pts 0) = 0 < 4224√15`). -/
theorem hface_wall :
    ∀ y ∈ Erdos634.Tiling44Bridge.targetTri.carrier, gWallAff y = 4224 * Real.sqrt 15 →
      y ∈ segment ℝ (Erdos634.Tiling44Bridge.targetTri.pts 1)
        (Erdos634.Tiling44Bridge.targetTri.pts 2) := by
  intro y hy hgy
  set T := Erdos634.Tiling44Bridge.targetTri
  set s : Finset Plane := {T.pts 0, T.pts 1, T.pts 2} with hs
  have hrange : Set.range T.pts = (s : Set Plane) := by
    rw [hs]
    ext x
    simp only [Set.mem_range, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩; fin_cases i <;> simp
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  have hxs : y ∈ convexHull ℝ (s : Set Plane) := by
    rw [← hrange]; exact hy
  have hle : ∀ v ∈ s, gWall v ≤ 4224 * Real.sqrt 15 := by
    intro v hv
    have hvmem : v ∈ Set.range T.pts := by rw [hrange]; exact hv
    obtain ⟨i, rfl⟩ := hvmem
    exact hwall_wall (T.pts i) (subset_convexHull ℝ _ (Set.mem_range_self i))
  have hfx : gWall y = 4224 * Real.sqrt 15 := hgy
  have hmax := Erdos634.SupportFace.mem_convexHull_max gWall (4224 * Real.sqrt 15) s hle hxs hfx
  have hfilter : s.filter (fun v => gWall v = 4224 * Real.sqrt 15) = {T.pts 1, T.pts 2} := by
    rw [hs]
    ext v
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hv, hgv⟩
      rcases hv with rfl | rfl | rfl
      · exfalso
        rw [tiling44_targetTri_pts0] at hgv
        rw [gWall_mkPt] at hgv
        nlinarith [Real.sqrt_nonneg (15:ℝ), Real.sq_sqrt (show (0:ℝ) ≤ 15 by norm_num)]
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · refine ⟨Or.inr (Or.inl rfl), ?_⟩
        rw [tiling44_targetTri_pts1, gWall_mkPt]; ring
      · refine ⟨Or.inr (Or.inr rfl), ?_⟩
        rw [tiling44_targetTri_pts2]
        rw [gWall_mkPt]; ring
  rw [hfilter] at hmax
  rw [Finset.coe_insert, Finset.coe_singleton, convexHull_pair] at hmax
  exact hmax

/-- **`hiso` for `(gWall, dirWall)`**: `dirWall` measures real distance exactly, for any two
points on the wall line. Both points lying on `gWall = 4224√15` forces their difference into
`gWall`'s kernel — the span of the wall's own direction vector `(-88, 24√15)`, of length exactly
`128` — and `dirWall`'s `/128` normalization is exactly what makes the two quantities coincide. -/
theorem hiso_wall :
    ∀ p q : Plane, gWallAff p = 4224 * Real.sqrt 15 → gWallAff q = 4224 * Real.sqrt 15 →
      dist p q = |dirWall p - dirWall q| := by
  intro p q hp hq
  have hp' : p = mkPt (xFun p) (yFun p) := by
    ext j; fin_cases j
    · show _ = xFun p; rfl
    · show _ = yFun p; rfl
  have hq' : q = mkPt (xFun q) (yFun q) := by
    ext j; fin_cases j
    · show _ = xFun q; rfl
    · show _ = yFun q; rfl
  have hgp : gWall p = 4224 * Real.sqrt 15 := hp
  have hgq : gWall q = 4224 * Real.sqrt 15 := hq
  rw [hp', gWall_mkPt] at hgp
  rw [hq', gWall_mkPt] at hgq
  have hs : Real.sqrt 15 ^ 2 = 15 := Real.sq_sqrt (by norm_num)
  set a := xFun p - xFun q with hadef
  set b := yFun p - yFun q with hbdef
  have hdiff : 24 * Real.sqrt 15 * a + 88 * b = 0 := by rw [hadef, hbdef]; linarith
  have hy_eq : b = -24 * Real.sqrt 15 / 88 * a := by
    field_simp
    linarith [hdiff]
  have hdsq : dist p q ^ 2 = a^2 + b^2 := by
    rw [hp', hq']; exact Erdos634.CertCoord.dist_sq_mkPt _ _ _ _
  have hdirp : dirWall p = (-88 * xFun p + 24 * Real.sqrt 15 * yFun p) / 128 := by
    rw [hp']; exact dirWall_mkPt _ _
  have hdirq : dirWall q = (-88 * xFun q + 24 * Real.sqrt 15 * yFun q) / 128 := by
    rw [hq']; exact dirWall_mkPt _ _
  have hdirdiff : dirWall p - dirWall q = (-88 * a + 24 * Real.sqrt 15 * b) / 128 := by
    rw [hdirp, hdirq]; ring
  have hdirdiff' : dirWall p - dirWall q = -16/11 * a := by
    rw [hdirdiff, hy_eq]
    have heq : -88 * a + 24 * Real.sqrt 15 * (-24 * Real.sqrt 15 / 88 * a)
        = -88 * a - (Real.sqrt 15 * Real.sqrt 15) * (24 * 24 / 88) * a := by ring
    rw [heq, Real.mul_self_sqrt (by norm_num : (15:ℝ) ≥ 0)]
    ring
  have hdsq' : dist p q ^ 2 = (16/11 * a)^2 := by
    rw [hdsq, hy_eq]
    have heq2 : a^2 + (-24 * Real.sqrt 15 / 88 * a)^2
        = a^2 * (1 + (Real.sqrt 15 * Real.sqrt 15) * (24/88)^2) := by ring
    rw [heq2, Real.mul_self_sqrt (by norm_num : (15:ℝ) ≥ 0)]
    ring
  rw [hdirdiff']
  have hdp : 0 ≤ dist p q := dist_nonneg
  have h1 : dist p q = Real.sqrt (dist p q ^ 2) := (Real.sqrt_sq hdp).symm
  rw [h1, hdsq', show (-16/11 * a) = -(16/11*a) by ring, abs_neg, ← Real.sqrt_sq_eq_abs]
