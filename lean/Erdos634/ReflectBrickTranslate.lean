import Erdos634.ReflectBrick
import Erdos634.TranslateDissection
import Erdos634.Realizable

/-!
# The brick construction transports through translation

Erdős #634. Toward `lem:wpgram`'s grid of translated brick copies: `ReflectBrick`'s brick
construction is fully general in the `Tri` `T`, so it applies equally to a translated copy of `T`
— but the *grid* needs translated copies to line up as translates of the same original brick, not
independently-constructed bricks that merely happen to be congruent. `reflectThroughEdge_mapTri`
shows `reflectThroughEdge` commutes with any affine equivalence (reflection and the equivalence
can be applied in either order), and `carrier_union_reflectThroughEdge1_translate` specializes
this to translation: gluing a translated tile to its own reflection gives exactly the translated
brick, not merely a congruent one — the fact the grid-tiling step needs to place brick copies by
simple vector addition and reuse `ReflectBrick`'s carrier identity at each one.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.AreaDet Erdos634.DissectionMap Erdos634.TranslateDissection

/-- `reflectThroughEdge` commutes with any affine equivalence: reflecting first and then mapping
gives the same triangle as mapping first and then reflecting through the image edge. -/
theorem reflectThroughEdge_mapTri (e : Plane ≃ᵃ[ℝ] Plane) (T : Tri) (k : Fin 3) :
    reflectThroughEdge (mapTri e T) k = mapTri e (reflectThroughEdge T k) := by
  apply Erdos634.Realizable.Tri.ext'
  funext i
  show ((AffineEquiv.pointReflection ℝ
      (midpoint ℝ ((mapTri e T).pts k) ((mapTri e T).pts (k+1)))) ∘ (mapTri e T).pts) i
    = (e ∘ (reflectThroughEdge T k).pts) i
  show (AffineEquiv.pointReflection ℝ
      (midpoint ℝ (e (T.pts k)) (e (T.pts (k+1))))) (e (T.pts i))
    = e ((AffineEquiv.pointReflection ℝ (midpoint ℝ (T.pts k) (T.pts (k+1)))) (T.pts i))
  have hmid : midpoint ℝ (e (T.pts k)) (e (T.pts (k+1))) = e (midpoint ℝ (T.pts k) (T.pts (k+1))) :=
    (AffineMap.map_midpoint e.toAffineMap (T.pts k) (T.pts (k+1))).symm
  rw [hmid, AffineEquiv.pointReflection_apply, AffineEquiv.pointReflection_apply]
  show (e (midpoint ℝ (T.pts k) (T.pts (k+1))) -ᵥ e (T.pts i))
      +ᵥ e (midpoint ℝ (T.pts k) (T.pts (k+1)))
    = e ((midpoint ℝ (T.pts k) (T.pts (k+1)) -ᵥ T.pts i) +ᵥ midpoint ℝ (T.pts k) (T.pts (k+1)))
  simp only [show (e : Plane → Plane) = e.toAffineMap from rfl, AffineMap.map_vadd,
    AffineMap.linearMap_vsub]

/-- **The brick tiling transports through translation.** Translating a `Tri` by `v` and then
gluing its own reflection is the same as translating the whole (untranslated) brick by `v`. -/
theorem carrier_union_reflectThroughEdge1_translate (T : Tri) (v : Plane) :
    (mapTri (transEquiv v).toAffineEquiv T).carrier
      ∪ (reflectThroughEdge (mapTri (transEquiv v).toAffineEquiv T) 1).carrier
      = (fun x => v + x) '' (T.carrier ∪ (reflectThroughEdge T 1).carrier) := by
  rw [reflectThroughEdge_mapTri, mapTri_carrier, mapTri_carrier, ← Set.image_union]
  congr 1
