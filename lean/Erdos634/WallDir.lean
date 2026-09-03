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

`hker_wallFun` closes the last algebraic hypothesis the same way: `wallFun`'s and `dirFun`'s
linear parts have trivial joint kernel, proved directly from the barycentric basis (a killed
vector forces `v +ᵥ T.pts k` to share every barycentric coordinate with `T.pts k`, hence to equal
it by `AffineBasis.ext_elem`).

This directly unblocks `side_walk_of_dissection` (hence `SidePRange.side_p_range`,
`lem:ccornerside`'s flank half, and `thm:walks`/`thm:walkstruct`/`cor:wallsf2e`'s own
"bridge (c)" gaps) for *any* real `CongruentDissection`, not only a specific certified member.
`hface` closes too: `mem_convexHull_max_affine` extends the pre-existing `SupportFace
.mem_convexHull_max` (which only handles *linear* functionals) to affine ones, via the standard
`f(y) = f(0) + f.linear(y)` decomposition on a module; `hface_wallFun` applies it to `wallFun T k`
over `T`'s three vertices.

Still open: `hthird` (genuinely dissection-specific, needs the actual tiling's combinatorics).

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

/-- **`side_walk_of_dissection`'s `hker` hypothesis, general for any `Tri` and side.** `wallFun`'s
and `dirFun`'s linear parts jointly have trivial kernel — proved directly from the barycentric
basis structure: a vector killed by both forces the point `v +ᵥ T.pts k` to share all three
barycentric coordinates with `T.pts k` itself, hence (by `AffineBasis.ext_elem`) to equal it. -/
theorem hker_wallFun (T : Tri) (k : Fin 3) :
    ∀ v : Plane, (wallFun T k).linear v = 0 → (dirFun T k).linear v = 0 → v = 0 := by
  intro v hv1 hv2
  have hc2 : (T.basis.coord (k+2)).linear v = 0 := by
    have heq : (wallFun T k).linear v = -(T.basis.coord (k+2)).linear v := rfl
    rw [heq] at hv1
    linarith
  have hc1 : (T.basis.coord (k+1)).linear v = 0 := by
    have heq : (dirFun T k).linear v = sideOpp T (k+2) * (T.basis.coord (k+1)).linear v := rfl
    rw [heq] at hv2
    have hSne : sideOpp T (k+2) ≠ 0 := by
      unfold sideOpp
      exact dist_ne_zero.mpr
        (Erdos634.TilePlacement.pts_ne T (show (k+2+1:Fin 3) ≠ k+2+2 from by fin_cases k <;> decide))
    exact (mul_eq_zero.mp hv2).resolve_left hSne
  set p := v +ᵥ T.pts k with hpdef
  have hbT : (T.basis : Fin 3 → Plane) k = T.pts k := rfl
  have hk1 : T.basis.coord (k+1) (T.pts k) = 0 := by
    rw [← hbT, AffineBasis.coord_apply_ne]; fin_cases k <;> decide
  have hk2 : T.basis.coord (k+2) (T.pts k) = 0 := by
    rw [← hbT, AffineBasis.coord_apply_ne]; fin_cases k <;> decide
  have hkk : T.basis.coord k (T.pts k) = 1 := by rw [← hbT, AffineBasis.coord_apply_eq]
  have hp1 : T.basis.coord (k+1) p = 0 := by
    rw [hpdef, AffineMap.map_vadd, vadd_eq_add, hc1, hk1]; ring
  have hp2 : T.basis.coord (k+2) p = 0 := by
    rw [hpdef, AffineMap.map_vadd, vadd_eq_add, hc2, hk2]; ring
  have hp0 : T.basis.coord k p = 1 := by
    have hsum := T.basis.sum_coord_apply_eq_one (k := ℝ) p
    rw [Fin.sum_univ_three] at hsum
    fin_cases k <;> simp_all <;> linarith
  have hpeq : p = T.pts k := by
    apply T.basis.ext_elem
    intro i
    fin_cases i
    · fin_cases k <;> [exact hp0.trans hkk.symm; exact hp2.trans hk2.symm; exact hp1.trans hk1.symm]
    · fin_cases k <;> [exact hp1.trans hk1.symm; exact hp0.trans hkk.symm; exact hp2.trans hk2.symm]
    · fin_cases k <;> [exact hp2.trans hk2.symm; exact hp1.trans hk1.symm; exact hp0.trans hkk.symm]
  have hveq : v +ᵥ T.pts k = T.pts k := hpdef ▸ hpeq
  rw [vadd_eq_add] at hveq
  linear_combination (norm := module) hveq

/-- **`SupportFace.mem_convexHull_max`, generalized from linear to affine functionals.** Points of
a convex hull attaining the maximum of an *affine* functional come from the vertices that attain
it — the same fact `SupportFace.mem_convexHull_max` proves for linear `f`, via the standard
`f(y) = f(0) + f.linear(y)` decomposition on a module. -/
theorem mem_convexHull_max_affine (f : Plane →ᵃ[ℝ] ℝ) (c : ℝ) (s : Finset Plane)
    (hle : ∀ v ∈ s, f v ≤ c) {x : Plane} (hx : x ∈ convexHull ℝ (s : Set Plane)) (hfx : f x = c) :
    x ∈ convexHull ℝ ((s.filter (fun v => f v = c) : Finset Plane) : Set Plane) := by
  classical
  rw [Finset.convexHull_eq] at hx
  obtain ⟨w, hw0, hw1, hcm⟩ := hx
  have hcomb : ∑ v ∈ s, w v • v = x := by
    rw [← hcm, Finset.centerMass_eq_of_sum_1 _ _ hw1]; rfl
  have hfaff : ∀ y : Plane, f y = f 0 + f.linear y := by
    intro y
    have h1 : f (y +ᵥ (0:Plane)) = f.linear y +ᵥ f 0 := AffineMap.map_vadd f 0 y
    rw [add_comm]; simpa using h1
  have hdef : ∑ v ∈ s, w v * (c - f v) = 0 := by
    have hfsum : ∑ v ∈ s, w v * f v = c := by
      have hkey : f (∑ v ∈ s, w v • v) = ∑ v ∈ s, w v * f v := by
        rw [hfaff (∑ v ∈ s, w v • v), map_sum]
        simp only [map_smul, smul_eq_mul]
        have heq2 : ∑ v ∈ s, w v * f.linear v = ∑ v ∈ s, w v * (f v - f 0) := by
          apply Finset.sum_congr rfl
          intro v _
          rw [hfaff v]; ring
        rw [heq2]
        have heq3 : ∑ v ∈ s, w v * (f v - f 0) = ∑ v ∈ s, w v * f v - (∑ v ∈ s, w v) * f 0 := by
          rw [Finset.sum_mul]
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun v _ => by ring)
        rw [heq3, hw1]; ring
      rw [hcomb] at hkey
      rw [← hkey, hfx]
    calc ∑ v ∈ s, w v * (c - f v)
        = (∑ v ∈ s, w v) * c - ∑ v ∈ s, w v * f v := by
          rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun v _ => by ring)
      _ = 0 := by rw [hw1, hfsum]; ring
  have hterm : ∀ v ∈ s, w v * (c - f v) = 0 := by
    refine (Finset.sum_eq_zero_iff_of_nonneg ?_).mp hdef
    intro v hv
    exact mul_nonneg (hw0 v hv) (by linarith [hle v hv])
  have hsupp : ∀ v ∈ s, w v ≠ 0 → f v = c := by
    intro v hv hne
    rcases mul_eq_zero.mp (hterm v hv) with h | h
    · exact absurd h hne
    · linarith
  have hzero : ∀ v ∈ s, v ∉ s.filter (fun v => f v = c) → w v = 0 := by
    intro v hv hnot
    by_contra hne
    exact hnot (Finset.mem_filter.mpr ⟨hv, hsupp v hv hne⟩)
  have hsub : s.filter (fun v => f v = c) ⊆ s := Finset.filter_subset _ _
  have hsum1 : ∑ v ∈ s.filter (fun v => f v = c), w v = 1 := by
    rw [Finset.sum_subset hsub hzero]; exact hw1
  rw [Finset.convexHull_eq]
  refine ⟨w, ?_, hsum1, ?_⟩
  · intro v hv; exact hw0 v (Finset.mem_filter.mp hv).1
  · rw [Finset.centerMass_eq_of_sum_1 _ _ hsum1]
    have hlast : ∑ v ∈ s.filter (fun v => f v = c), w v • id v = ∑ v ∈ s, w v • v := by
      refine Finset.sum_subset hsub ?_
      intro v hv hnot; simp [hzero v hv hnot]
    rw [hlast]; exact hcomb

/-- **`side_walk_of_dissection`'s `hface` hypothesis, general for any `Tri` and side.** Any target
point attaining the wall's own maximum lies on the side's own segment. -/
theorem hface_wallFun (T : Tri) (k : Fin 3) :
    ∀ y ∈ T.carrier, wallFun T k y = 0 → y ∈ segment ℝ (T.pts k) (T.pts (k+1)) := by
  intro y hy hgy
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
  have hle : ∀ v ∈ s, wallFun T k v ≤ 0 := by
    intro v hv
    have hvmem : v ∈ Set.range T.pts := by rw [hrange]; exact hv
    obtain ⟨i, rfl⟩ := hvmem
    exact wallFun_le T k (subset_convexHull ℝ _ (Set.mem_range_self i))
  have hmax := mem_convexHull_max_affine (wallFun T k) 0 s hle hxs hgy
  have hbT : ∀ i : Fin 3, (T.basis : Fin 3 → Plane) i = T.pts i := fun i => rfl
  have hcoord_eq0 : ∀ i : Fin 3, T.basis.coord i (T.pts i) = 1 := fun i => by
    rw [← hbT i, AffineBasis.coord_apply_eq]
  have hwall_ne : ∀ i : Fin 3, wallFun T i (T.pts (i+2)) ≠ 0 := by
    intro i
    show -(T.basis.coord (i+2)) (T.pts (i+2)) ≠ 0
    rw [hcoord_eq0]
    norm_num
  have hfilter : s.filter (fun v => wallFun T k v = 0) = {T.pts k, T.pts (k+1)} := by
    rw [hs]
    ext v
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hv, hgv⟩
      rcases hv with rfl | rfl | rfl <;> fin_cases k <;>
        first
          | (left; rfl) | (right; rfl)
          | (exact absurd hgv (hwall_ne _))
    · rintro (rfl | rfl)
      · refine ⟨?_, wallFun_eq_zero T k (left_mem_segment ℝ _ _)⟩
        fin_cases k <;> simp
      · refine ⟨?_, wallFun_eq_zero T k (right_mem_segment ℝ _ _)⟩
        fin_cases k <;> simp
  rw [hfilter] at hmax
  rw [Finset.coe_insert, Finset.coe_singleton, convexHull_pair] at hmax
  exact hmax
