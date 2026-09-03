import Erdos634.SideWall
import Erdos634.TilePlacement

/-!
# The general, coordinate-free `hiso` calibration for any triangle's wall line

Erdős #634. `SideWall.wallFun` already builds `hker`/`hwall`'s functional `g` for any `Tri` and
any side, with no explicit coordinates. `SideWalk.side_walk_of_dissection` also needs `dir` and
`hiso` (`dist p q = |dir p - dir q|` for `p, q` on the wall line) — every past instantiation of
this project (`Tiling44WallSetup.lean`'s `dirWall`/`hiso_wall`) built these by hand from explicit
`√15`-certificate coordinates, one fixed target at a time.

This file builds them in full generality instead: `eq_lineMap_of_wallFun_eq_zero` shows any point
on the wall line is `lineMap (T.pts k) (T.pts (k+1))` at its own `(k+1)`-barycentric coordinate
(via `AffineBasis.affineCombination_coord_eq_self` plus `Mathlib`'s `mem_affineSpan_pair`-style
line parametrization, worked directly through vector algebra), and `dirFun`/`hiso_wallFun`
calibrate that coordinate by the side's own length (`Mathlib`'s `dist_lineMap_lineMap`) to get
real Euclidean distance — for *any* `Tri` and *any* side, no coordinates, no fixed target.

This directly unblocks `side_walk_of_dissection` (hence `SidePRange.side_p_range`,
`lem:ccornerside`'s flank half, and `thm:walks`/`thm:walkstruct`/`cor:wallsf2e`'s own
"bridge (c)" gaps) for *any* real `CongruentDissection`, not only a specific certified member.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.SideWall Erdos634.TilePlacement

/-- **Any point on a triangle's wall line is `lineMap` between the side's own two vertices**, at
the parameter given by its own barycentric coordinate. General for any `Tri` and any side `k`, no
coordinates needed. -/
theorem eq_lineMap_of_wallFun_eq_zero (T : Tri) (k : Fin 3) {p : Plane} (hp : wallFun T k p = 0) :
    p = AffineMap.lineMap (T.pts k) (T.pts (k+1)) (T.basis.coord (k+1) p) := by
  have hcoord2 : T.basis.coord (k+2) p = 0 := by simpa [wallFun] using hp
  have hrepr := T.basis.affineCombination_coord_eq_self p
  rw [Finset.affineCombination_eq_linear_combination _ _ _
    (T.basis.sum_coord_apply_eq_one (k := ℝ) p)] at hrepr
  rw [Fin.sum_univ_three] at hrepr
  have hsum := T.basis.sum_coord_apply_eq_one (k := ℝ) p
  rw [Fin.sum_univ_three] at hsum
  rw [AffineMap.lineMap_apply]
  show p = (T.basis.coord (k+1) p) • (T.pts (k+1) -ᵥ T.pts k) +ᵥ T.pts k
  rw [vadd_eq_add, vsub_eq_sub]
  have hbT : ∀ i, (T.basis : Fin 3 → Plane) i = T.pts i := fun i => rfl
  rw [hbT, hbT, hbT] at hrepr
  fin_cases k
  · show p = T.basis.coord 1 p • (T.pts 1 - T.pts 0) + T.pts 0
    have hc2 : T.basis.coord (2:Fin 3) p = 0 := hcoord2
    have hs2 : T.basis.coord (0:Fin 3) p + T.basis.coord 1 p + T.basis.coord 2 p = 1 := hsum
    rw [hc2, zero_smul, add_zero] at hrepr
    nth_rewrite 1 [← hrepr]
    rw [hc2] at hs2
    have hval : T.basis.coord (0:Fin 3) p = 1 - T.basis.coord 1 p := by linarith
    rw [hval]; module
  · show p = T.basis.coord 2 p • (T.pts 2 - T.pts 1) + T.pts 1
    have hc2 : T.basis.coord (0:Fin 3) p = 0 := hcoord2
    have hs2 : T.basis.coord (0:Fin 3) p + T.basis.coord 1 p + T.basis.coord 2 p = 1 := hsum
    rw [hc2, zero_smul, zero_add] at hrepr
    nth_rewrite 1 [← hrepr]
    rw [hc2] at hs2
    have hval : T.basis.coord (1:Fin 3) p = 1 - T.basis.coord 2 p := by linarith
    rw [hval]; module
  · show p = T.basis.coord 0 p • (T.pts 0 - T.pts 2) + T.pts 2
    have hc2 : T.basis.coord (1:Fin 3) p = 0 := hcoord2
    have hs2 : T.basis.coord (0:Fin 3) p + T.basis.coord 1 p + T.basis.coord 2 p = 1 := hsum
    rw [hc2, zero_smul] at hrepr
    simp only [add_zero] at hrepr
    nth_rewrite 1 [← hrepr]
    rw [hc2] at hs2
    have hval : T.basis.coord (2:Fin 3) p = 1 - T.basis.coord 0 p := by linarith
    rw [hval]; module

/-- **The direction functional of side `k`**: the barycentric coordinate of `k+1`, scaled by the
side's own length (`sideOpp T (k+2)`, since `sideOpp T j = dist (pts (j+1)) (pts (j+2))`), so it
measures real distance along the wall line. General for any `Tri`, no coordinates. -/
noncomputable def dirFun (T : Tri) (k : Fin 3) : Plane →ᵃ[ℝ] ℝ :=
  (sideOpp T (k+2)) • (T.basis.coord (k+1))

/-- **`dirFun` is calibrated to real distance on the whole wall line**: any two points with
`wallFun T k = 0` have their distance equal to the absolute difference of `dirFun`. This is
`side_walk_of_dissection`'s `hiso` hypothesis, general for any `Tri` and side, no coordinates —
what every past instantiation of this project (`Tiling44WallSetup.hiso_wall`) built by hand for
one fixed target. -/
theorem hiso_wallFun (T : Tri) (k : Fin 3) {p q : Plane}
    (hp : wallFun T k p = 0) (hq : wallFun T k q = 0) :
    dist p q = |dirFun T k p - dirFun T k q| := by
  rw [eq_lineMap_of_wallFun_eq_zero T k hp, eq_lineMap_of_wallFun_eq_zero T k hq,
    dist_lineMap_lineMap]
  show dist (T.basis.coord (k+1) p) (T.basis.coord (k+1) q) * dist (T.pts k) (T.pts (k+1))
    = |dirFun T k (AffineMap.lineMap (T.pts k) (T.pts (k+1)) (T.basis.coord (k+1) p))
      - dirFun T k (AffineMap.lineMap (T.pts k) (T.pts (k+1)) (T.basis.coord (k+1) q))|
  rw [← eq_lineMap_of_wallFun_eq_zero T k hp, ← eq_lineMap_of_wallFun_eq_zero T k hq]
  show |T.basis.coord (k+1) p - T.basis.coord (k+1) q| * dist (T.pts k) (T.pts (k+1))
    = |dirFun T k p - dirFun T k q|
  have hdd : dist (T.pts k) (T.pts (k+1)) = sideOpp T (k+2) := by
    show dist (T.pts k) (T.pts (k+1)) = dist (T.pts (k+2+1)) (T.pts (k+2+2))
    have h1 : (k+2+1 : Fin 3) = k := by fin_cases k <;> decide
    have h2 : (k+2+2 : Fin 3) = k+1 := by fin_cases k <;> decide
    rw [h1, h2]
  rw [hdd]
  show |T.basis.coord (k+1) p - T.basis.coord (k+1) q| * sideOpp T (k+2)
    = |sideOpp T (k+2) * T.basis.coord (k+1) p - sideOpp T (k+2) * T.basis.coord (k+1) q|
  have hSpos : 0 < sideOpp T (k+2) := by
    unfold sideOpp
    exact dist_pos.mpr
      (Erdos634.TilePlacement.pts_ne T (show (k+2+1:Fin 3) ≠ k+2+2 from by fin_cases k <;> decide))
  rw [show sideOpp T (k+2) * T.basis.coord (k+1) p - sideOpp T (k+2) * T.basis.coord (k+1) q
    = sideOpp T (k+2) * (T.basis.coord (k+1) p - T.basis.coord (k+1) q) from by ring,
    abs_mul, abs_of_pos hSpos, mul_comm]
