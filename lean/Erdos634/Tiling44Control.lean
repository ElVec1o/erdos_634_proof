import Erdos634.Tiling44Bridge
import Erdos634.SixPlacements
import Erdos634.ThickBlockingLemmas

/-!
# Control: `placement_completeness` on the real 44-tiling

Erdős #634.  `PlacementCompleteness.placement_completeness` must be *satisfiable* — its hypotheses
must be dischargeable on a real dissection — or it proves nothing (the `word42_junction_dies`
lesson).  This file discharges them on `Tiling44Bridge.dissection`, the kernel-checked
`(16,16,22)`-by-`(2,3,4)` tiling (scaled by 8: target `(0,0),(176,0),(88,24√15)`, tile sides
`16, 24, 32`), with `S = ∅`:

* the lexicographically least point of the target is its origin `(0,0)`; the clockwise boundary
  ray there is `(1,0)` (the base); the counter-clockwise side is inside the target, the clockwise
  side is below it;
* `control_root` — the theorem then yields a tile with a corner at `(0,0)`, an edge along `(1,0)`
  and third vertex above — as it must;
* `tile0_is_the_placement` — the actual tile is `Tiling44.tiles[0] = (0,0),(16,0),(22,6√15)`, and
  its third vertex is `placeThird (0,0) (1,0) 16 32 24` — the `(a, c, b)` placement of
  `six_placements` (side `16` along the ray, side `32` the other side at the corner).

Axiom-clean; no `sorry`.
-/

namespace Erdos634.Tiling44Control

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.Z15Real
  Erdos634.Tiling44Bridge Erdos634.PlacementCompleteness Erdos634.SixPlacements

/-- The target's three vertices, as real numbers. -/
theorem target_coords :
    toR (zx (toZPt (Tiling44.t1 Tiling44.target))) = 0 ∧
    toR (zy (toZPt (Tiling44.t1 Tiling44.target))) = 0 ∧
    toR (zx (toZPt (Tiling44.t2 Tiling44.target))) = 176 ∧
    toR (zy (toZPt (Tiling44.t2 Tiling44.target))) = 0 ∧
    toR (zx (toZPt (Tiling44.t3 Tiling44.target))) = 88 ∧
    toR (zy (toZPt (Tiling44.t3 Tiling44.target))) = 24 * Real.sqrt 15 := by
  simp [toR, zx, zy, toZPt, Tiling44.target, Tiling44.t1, Tiling44.t2, Tiling44.t3]

theorem sqrt15_bounds : 3 < Real.sqrt 15 ∧ Real.sqrt 15 < 4 := by
  constructor <;> nlinarith [sqrt15_sq, sqrt15_pos]

theorem det_target : det3 (0:ℝ) 0 176 0 88 (24 * Real.sqrt 15) ≠ 0 := by
  unfold det3; nlinarith [sqrt15_pos]

/-- The target with explicit coordinates. -/
theorem targetTri_eq : targetTri = mkTri (0:ℝ) 0 176 0 88 (24 * Real.sqrt 15) det_target := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := target_coords
  unfold targetTri
  congr 1

theorem mkPt_self (p : Plane) : mkPt (p 0) (p 1) = p := plane_ext (by simp) (by simp)

theorem target_y_nonneg {p : Plane} (hp : p ∈ targetTri.carrier) : 0 ≤ p 1 := by
  have hb : ∀ z ∈ targetTri.carrier, lineFun 176 0 0 0 z ≤ 0 := by
    refine le_of_forall_pts_le _ ?_
    intro k
    rw [targetTri_eq]
    fin_cases k <;> simp [mkTri_pts, mkPt_zero, mkPt_one, lineFun_apply] <;> nlinarith [sqrt15_pos]
  have := hb p hp
  simp only [lineFun_apply] at this
  linarith

theorem target_left {p : Plane} (hp : p ∈ targetTri.carrier) :
    0 ≤ 24 * Real.sqrt 15 * p 0 - 88 * p 1 := by
  have hb : ∀ z ∈ targetTri.carrier, 0 ≤ lineFun 88 (24 * Real.sqrt 15) 0 0 z := by
    refine Erdos634.ThickBlockingLemmas.ge_of_forall_pts_ge _ ?_
    intro k
    rw [targetTri_eq]
    fin_cases k <;> simp [mkTri_pts, mkPt_zero, mkPt_one, lineFun_apply] <;> nlinarith [sqrt15_pos]
  have := hb p hp
  simp only [lineFun_apply] at this
  linarith

/-- The unfilled region with nothing placed is the target. -/
theorem unfilled_empty {N : ℕ} (D : Dissection N) : unfilled D ∅ = D.target.carrier := by
  simp [unfilled]

/-- The origin and the base direction. -/
noncomputable def v0 : Plane := mkPt 0 0
noncomputable def d0 : Plane := mkPt 1 0

theorem d0_unit : d0 0 ^ 2 + d0 1 ^ 2 = 1 := by simp [d0]

theorem pt_ccw (t s : ℝ) : v0 + t • (d0 + s • perp d0) = mkPt t (t * s) := by
  refine plane_ext ?_ ?_ <;> simp [v0, d0]

theorem pt_cw (t s : ℝ) : v0 + t • (d0 - s • perp d0) = mkPt t (-(t * s)) := by
  refine plane_ext ?_ ?_ <;> simp [v0, d0]

/-- **The control.**  On the real 44-tiling with nothing placed, the hypotheses of
`placement_completeness` hold at `v = (0,0)`, `d = (1,0)`, and the theorem produces a tile with a
corner at the origin, an edge along the base, third vertex above. -/
theorem control_root :
    ∃ j, j ∉ (∅ : Finset (Fin Tiling44.tiles.length)) ∧ ∃ k₀ k₁ k₂ : Fin 3,
      k₀ ≠ k₁ ∧ k₀ ≠ k₂ ∧ k₁ ≠ k₂ ∧
      (dissection.tile j).pts k₀ = v0 ∧
      (∃ c : ℝ, 0 < c ∧ (dissection.tile j).pts k₁ = v0 + c • d0) ∧
      0 < cross d0 ((dissection.tile j).pts k₂ - v0) := by
  obtain ⟨hs3, hs4⟩ := sqrt15_bounds
  have hUt : unfilled dissection.toDissection ∅ = targetTri.carrier := unfilled_empty _
  refine placement_completeness dissection.toDissection ∅ v0 d0 d0_unit ?_ ?_ ?_
  · -- lexicographic minimality of the origin on the (closed) target
    intro p hp
    rw [hUt, targetTri.isCompact.isClosed.closure_eq] at hp
    have hy := target_y_nonneg hp
    have hl := target_left hp
    simp only [LexLE, v0, mkPt_zero, mkPt_one]
    rcases lt_or_eq_of_le hy with h | h
    · exact Or.inl h
    · refine Or.inr ⟨h, ?_⟩
      rw [← h] at hl
      nlinarith [sqrt15_pos]
  · -- the counter-clockwise side is inside the target
    intro ε hε
    have hmin : min (ε / 2) (1 / 4) < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    refine ⟨min (ε / 2) (1 / 4), min (ε / 2) (1 / 4), by positivity, hmin, by positivity, hmin, ?_⟩
    set t := min (ε / 2) (1 / 4) with ht
    have ht0 : 0 < t := by positivity
    have ht1 : t ≤ 1 / 4 := min_le_right _ _
    rw [hUt, pt_ccw, targetTri_eq]
    refine mem_carrier_of_dets (x₀ := 0) (y₀ := 0) (x₁ := 176) (y₁ := 0) (x₂ := 88)
      (y₂ := 24 * Real.sqrt 15) ?_ ?_ ?_ ?_
    · unfold det3; nlinarith [sqrt15_pos]
    · unfold det3; nlinarith [mul_pos ht0 sqrt15_pos, mul_pos ht0 ht0]
    · unfold det3; nlinarith [mul_pos ht0 sqrt15_pos, mul_pos ht0 ht0]
    · unfold det3; nlinarith [mul_pos ht0 ht0]
  · -- the clockwise side is below the base
    refine ⟨1, one_pos, fun t s ht _ hs _ => ?_⟩
    rw [hUt, pt_cw]
    intro h
    have := target_y_nonneg h
    simp only [mkPt_one] at this
    nlinarith [mul_pos ht hs]

/-- `dissection`'s tiles are the certificate's pieces. -/
theorem tile_eq (i : Fin Tiling44.tiles.length) : dissection.tile i = pieceAt i := rfl

theorem tiles_length : Tiling44.tiles.length = 44 := by decide

/-- The index of the first tile. -/
def idx0 : Fin Tiling44.tiles.length := ⟨0, by rw [tiles_length]; norm_num⟩

theorem tile0_pts :
    (dissection.tile idx0).pts 0 = mkPt 0 0 ∧
    (dissection.tile idx0).pts 1 = mkPt 16 0 ∧
    (dissection.tile idx0).pts 2 = mkPt 22 (6 * Real.sqrt 15) := by
  rw [tile_eq]
  unfold pieceAt
  refine ⟨?_, ?_, ?_⟩ <;> rw [pieceTri_pts] <;>
    simp [vertexOf, toR, zx, zy, toZPt, idx0, Tiling44.tiles, Tiling44.t1, Tiling44.t2,
      Tiling44.t3]

/-- **The actual next tile is the `(a, c, b)` placement**: `Tiling44.tiles[0]` has its corner at
the origin, its side of length `16` along the base, and its third vertex at
`placeThird (0,0) (1,0) 16 32 24 = (22, 6√15)`. -/
theorem tile0_is_the_placement :
    (dissection.tile idx0).pts 0 = v0 ∧
    (dissection.tile idx0).pts 1 = v0 + (16:ℝ) • d0 ∧
    (dissection.tile idx0).pts 2 = placeThird v0 d0 16 32 24 ∧
    0 < cross d0 ((dissection.tile idx0).pts 2 - v0) := by
  obtain ⟨h0, h1, h2⟩ := tile0_pts
  refine ⟨h0, ?_, ?_, ?_⟩
  · rw [h1]; refine plane_ext ?_ ?_ <;> simp [v0, d0]
  · rw [h2, placeThird]
    have hsq : (32:ℝ) ^ 2 - ((16 ^ 2 + 32 ^ 2 - 24 ^ 2) / (2 * 16)) ^ 2 = (6 * Real.sqrt 15) ^ 2 := by
      nlinarith [sqrt15_sq]
    rw [hsq, Real.sqrt_sq (by positivity)]
    refine plane_ext ?_ ?_ <;> simp [v0, d0] <;> norm_num
  · rw [h2]; simp [cross, v0, d0]

end Erdos634.Tiling44Control

#print axioms Erdos634.Tiling44Control.control_root
#print axioms Erdos634.Tiling44Control.tile0_is_the_placement
