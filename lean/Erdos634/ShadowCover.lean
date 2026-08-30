import Erdos634.WallEdges
import Erdos634.ChainInstance

/-!
# The base's shadow is covered by the edges' shadows

Erdős #634, bridge (c).  `WallEdges.base_covered_by_wall_edges` covers the base by wall edges as
sets of points.  `ChainInstance.consecutive_edges_meet` wants the covering one level down, as an
inclusion of intervals in `ℝ`.  Applying the wall's coordinate functional to both sides of the
first gives the second, since the image of a segment is the interval between its endpoints'
coordinates (`ChainInstance.edge_image_eq_Icc`).

Axiom-clean; no `sorry`.
-/

namespace Erdos634.ShadowCover

open Erdos634.Geometry Erdos634.OrientBridge Erdos634.ChainInstance Set

/-- **The shadow covering.**  The image of the base under the wall's coordinate functional is
covered by the intervals `[edgePos, edgeEnd]` of the wall edges. -/
theorem shadow_cover {N : ℕ} (D : Dissection N) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ)
    (dir : Plane →ₗ[ℝ] ℝ)
    (hwall : ∀ y ∈ D.target.carrier, g y ≤ c) (a b : Plane) (hab : a ≠ b)
    (hbase : segment ℝ a b ⊆ frontier D.target.carrier)
    (hline : ∀ y ∈ segment ℝ a b, g y = c) :
    uIcc (dir a) (dir b) ⊆
      ⋃ p ∈ {p : Fin N × Fin 3 | Erdos634.WallEdges.WallEdge D g c p},
        Icc (edgePos D dir p) (edgeEnd D dir p) := by
  have hbase' := Erdos634.WallEdges.base_covered_by_wall_edges D g c hwall a b hab hbase hline
  have himg : dir '' (segment ℝ a b) = uIcc (dir a) (dir b) := by
    have h := image_segment ℝ dir.toAffineMap a b
    simp only [LinearMap.coe_toAffineMap] at h
    rw [h, segment_eq_uIcc]
  rw [← himg]
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp (hbase' hx)
  refine mem_iUnion₂.mpr ⟨p, hp, ?_⟩
  rw [← edge_image_eq_Icc]
  exact ⟨x, hxp, rfl⟩

end Erdos634.ShadowCover
