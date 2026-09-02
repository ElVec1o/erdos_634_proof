import Erdos634.AreaDet

/-!
# Point-reflecting a triangle through an edge: the general "brick" construction

Erdős #634. Toward `lem:wpgram` (the W-parallelogram at general `f`): the "c-glued two-tile
brick" is a triangle glued to its own point-reflection through the midpoint of one edge, forming a
parallelogram. This file builds that construction for a *general* `Tri`, with no explicit
coordinates — reusing `AreaDet`'s existing `placeMap`/`stdCarrier`/`stdCarrier2` machinery (the
affine-image-of-the-unit-square route `PgramTiling22Bridge` found for its own (C2) gap) rather
than a hand-rolled diagonal-split argument. This is the general form of the diagonal-split lemma
originally scoped for `PgramTiling22Bridge`'s (C2) gap — superseded there by a better route, but
worth having in general form for a genuinely new target.

`reflectThroughEdge T k` reflects `T` through the midpoint of edge `(T.pts k, T.pts (k+1))`: it
fixes that edge (swapping its endpoints) and sends the third vertex to `T.pts k + T.pts (k+1) -
T.pts (k+2)`. `carrier_union_reflectThroughEdge1` identifies `T.carrier ∪ (reflectThroughEdge T
1).carrier` — the brick — as `placeMap T '' stdSquare`, the affine image of the unit square under
the same map that carries the reference triangle onto `T`.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.AreaDet

/-- Point-reflecting a `Tri` through the midpoint of edge `(k, k+1)`: fixes that edge (swapping
endpoints), sends the third vertex to its mirror image. -/
noncomputable def reflectThroughEdge (T : Tri) (k : Fin 3) : Tri where
  pts := (AffineEquiv.pointReflection ℝ (midpoint ℝ (T.pts k) (T.pts (k+1)))) ∘ T.pts
  indep := by
    have := T.indep
    exact this.map' (AffineEquiv.pointReflection ℝ (midpoint ℝ (T.pts k) (T.pts (k+1)))).toAffineMap
      (AffineEquiv.pointReflection ℝ (midpoint ℝ (T.pts k) (T.pts (k+1)))).injective

theorem reflectThroughEdge_pts (T : Tri) (k : Fin 3) (i : Fin 3) :
    (reflectThroughEdge T k).pts i
      = (AffineEquiv.pointReflection ℝ (midpoint ℝ (T.pts k) (T.pts (k+1)))) (T.pts i) := rfl

theorem midpoint_eq_half_sum (T : Tri) (k : Fin 3) :
    midpoint ℝ (T.pts k) (T.pts (k+1)) = (2:ℝ)⁻¹ • (T.pts k + T.pts (k+1)) := by
  rw [midpoint_eq_smul_add]; norm_num

/-- The reflection fixes vertex `k+1`'s image at `k`: the reflected triangle's `k`-th vertex is
the original's `k+1`-th. -/
theorem reflectThroughEdge_fixes_k (T : Tri) (k : Fin 3) :
    (reflectThroughEdge T k).pts k = T.pts (k+1) := by
  rw [reflectThroughEdge_pts, AffineEquiv.pointReflection_apply]
  show (midpoint ℝ (T.pts k) (T.pts (k + 1)) -ᵥ T.pts k) +ᵥ midpoint ℝ (T.pts k) (T.pts (k+1))
    = T.pts (k+1)
  rw [vsub_eq_sub, vadd_eq_add, midpoint_eq_half_sum]
  module

theorem reflectThroughEdge_fixes_k1 (T : Tri) (k : Fin 3) :
    (reflectThroughEdge T k).pts (k+1) = T.pts k := by
  rw [reflectThroughEdge_pts, AffineEquiv.pointReflection_apply]
  show (midpoint ℝ (T.pts k) (T.pts (k + 1)) -ᵥ T.pts (k+1)) +ᵥ midpoint ℝ (T.pts k) (T.pts (k+1))
    = T.pts k
  rw [vsub_eq_sub, vadd_eq_add, midpoint_eq_half_sum]
  module

/-- The third vertex reflects to its mirror image `T.pts k + T.pts (k+1) - T.pts (k+2)`. -/
theorem reflectThroughEdge_third (T : Tri) (k : Fin 3) :
    (reflectThroughEdge T k).pts (k+2) = T.pts k + T.pts (k+1) - T.pts (k+2) := by
  rw [reflectThroughEdge_pts, AffineEquiv.pointReflection_apply]
  show (midpoint ℝ (T.pts k) (T.pts (k + 1)) -ᵥ T.pts (k+2)) +ᵥ midpoint ℝ (T.pts k) (T.pts (k+1))
    = T.pts k + T.pts (k+1) - T.pts (k+2)
  rw [vsub_eq_sub, vadd_eq_add, midpoint_eq_half_sum]
  module

theorem placeMap_reflC (T : Tri) : placeMap T reflC = T.pts 1 + T.pts 2 - T.pts 0 := by
  show placeMap T (pb 0 + pb 1) = T.pts 1 + T.pts 2 - T.pts 0
  rw [placeMap_apply, map_add, edgeMap_basis, edgeMap_basis]
  show T.pts 0 + ((T.pts 1 - T.pts 0) + (T.pts 2 - T.pts 0)) = T.pts 1 + T.pts 2 - T.pts 0
  abel

/-- **The triangle reflected through edge `(1,2)` is exactly the affine image of `stdCarrier2`**
under the same map that carries the reference triangle onto `T`. -/
theorem reflectThroughEdge1_carrier (T : Tri) :
    (reflectThroughEdge T 1).carrier = placeMap T '' stdCarrier2 := by
  show convexHull ℝ (Set.range (reflectThroughEdge T 1).pts) = placeMap T '' stdCarrier2
  have hrange : Set.range (reflectThroughEdge T 1).pts
      = Set.range (placeMap T ∘ ![reflC, pb 1, pb 0]) := by
    apply congrArg Set.range
    funext i
    fin_cases i
    · show (reflectThroughEdge T 1).pts 0 = placeMap T reflC
      have h02 : (reflectThroughEdge T 1).pts 0 = (reflectThroughEdge T 1).pts (1+2) := by
        congr 1
      have h11 : (1:Fin 3) + 1 = 2 := by decide
      have h12 : (1:Fin 3) + 2 = 0 := by decide
      rw [h02, reflectThroughEdge_third, placeMap_reflC, h11, h12]
    · show (reflectThroughEdge T 1).pts 1 = placeMap T (pb 1)
      rw [reflectThroughEdge_fixes_k]
      have h11 : (1:Fin 3) + 1 = 2 := by decide
      rw [h11, placeMap_apply, edgeMap_basis]
      show T.pts 2 = T.pts 0 + (T.pts 2 - T.pts 0)
      abel
    · show (reflectThroughEdge T 1).pts 2 = placeMap T (pb 0)
      have h2 : (2:Fin 3) = 1 + 1 := by decide
      rw [h2, reflectThroughEdge_fixes_k1]
      rw [placeMap_apply, edgeMap_basis]
      show T.pts 1 = T.pts 0 + (T.pts 1 - T.pts 0)
      abel
  rw [hrange, Set.range_comp, stdCarrier2, ← AffineMap.image_convexHull]

/-- **The "c-glued brick" is the affine image of the unit square.** `T` glued to its own
reflection through edge `(1,2)` exactly tiles the parallelogram `placeMap T '' stdSquare` — the
general form of `lem:wpgram`'s "c-glued two-tile brick", with no explicit coordinates needed. -/
theorem carrier_union_reflectThroughEdge1 (T : Tri) :
    T.carrier ∪ (reflectThroughEdge T 1).carrier = placeMap T '' stdSquare := by
  rw [← placeMap_stdCarrier T, reflectThroughEdge1_carrier, ← Set.image_union,
    stdCarrier_union_stdCarrier2]
