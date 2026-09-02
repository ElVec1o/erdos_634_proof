import Erdos634.PgramTiling22Bridge
import Erdos634.TranslateDissection
import Erdos634.Tiling44Bridge
import Erdos634.CertCoord

/-!
# The `m=2 → m=4` collar step — placed-piece coordinates, checked

Erdős #634. `thm:realize12`'s existence half needs `Δ_4` (`N=176=11·4²`) built from `Δ_2`
(`Tiling44Bridge.dissection`) and a collar, per `lem:collar`'s decomposition. `UnionDissection`
turned out inapplicable (the collar's intermediate regions — a column, the collar as a whole —
are not triangles, and `Dissection`'s target field is `Tri`-only); the real route is a flat-list
certificate for all `176` translated pieces, built directly (as `Tiling44Bridge`/
`PgramTiling22Bridge` themselves are), using `TranslateDissection`'s placement primitive.

This file checks the exact placement geometry worked out by hand
(`private/VERIFY_PLAN.md`'s 2026-09-05 entries), against the real coordinate data, **before**
attempting the (much larger) containment/disjointness/area-sum proof for the combined list:

* `pgram_scaled_corners`: `PgramTiling22`'s four corners, rescaled `×2` (to match `Tiling44`'s `×8`
  `ℤ[√15]` convention), land at `(0,0)`, `(88,0)`, `(132,12√15)`, `(44,12√15)` — the base position of
  column `0`'s bottom `P_1` copy.
* `apex_copy_pts`: `Tiling44Bridge.dissection` translated by `(88, 24√15)` — the candidate
  `Δ_2^apex` — has vertices `(88,24√15)`, `(264,24√15)`, apex `(176,48√15)`, matching the
  hand-derived corner-anchored-at-`Δ_4`'s-own-apex computation exactly.
* `corner_copy_pts`: `Tiling44Bridge.dissection` translated by `(176, 0)` — the corner triangle on
  base `[176,352]` — has vertices `(176,0)`, `(352,0)`, `(264,24√15)`.

All three checks succeed exactly as hand-predicted; the collar's other placements (each column's
two halves, four in total, and column `1`) follow the same pattern by an additional shift of
`(88j, 0)` and `(44, 12√15)` per copy, not yet built.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.DissectionMap Erdos634.TranslateDissection Erdos634.CertCoord

theorem mkPt_add (x1 y1 x2 y2 : ℝ) : mkPt x1 y1 + mkPt x2 y2 = mkPt (x1 + x2) (y1 + y2) := by
  ext i; fin_cases i <;> simp [PiLp.add_apply, mkPt_zero, mkPt_one]

theorem smul_mkPt (c x y : ℝ) : c • mkPt x y = mkPt (c * x) (c * y) := by
  ext i; fin_cases i <;> simp [PiLp.smul_apply, mkPt_zero, mkPt_one]

/-- The four `PgramTiling22` corners, rescaled ×2, match the m=4 column base positions
hand-derived for the collar step. -/
theorem pgram_scaled_corners :
    (2:ℝ) • Erdos634.PgramTiling22Bridge.v1 = mkPt 0 0 ∧
    (2:ℝ) • Erdos634.PgramTiling22Bridge.v2 = mkPt 88 0 ∧
    (2:ℝ) • Erdos634.PgramTiling22Bridge.v3 = mkPt 132 (12 * Real.sqrt 15) ∧
    (2:ℝ) • Erdos634.PgramTiling22Bridge.v4 = mkPt 44 (12 * Real.sqrt 15) := by
  have key : ∀ (q : PgramTiling22.Pt) (a b c d : ℤ),
      (Erdos634.Z15Real.zx (q : Erdos634.Z15Real.ZPt) = (a, 0) ∧
       Erdos634.Z15Real.zy (q : Erdos634.Z15Real.ZPt) = (0, b)) →
      (2:ℝ) • mkPt (Erdos634.Z15Real.toR (Erdos634.Z15Real.zx (q : Erdos634.Z15Real.ZPt)))
        (Erdos634.Z15Real.toR (Erdos634.Z15Real.zy (q : Erdos634.Z15Real.ZPt)))
      = mkPt ((a:ℝ) * 2) ((b:ℝ) * 2 * Real.sqrt 15) := by
    intro q a b c d ⟨hx, hy⟩
    rw [hx, hy]; simp only [Erdos634.Z15Real.toR]; push_cast
    rw [smul_mkPt]; congr 1 <;> ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := key PgramTiling22.q1 0 0 0 0 (by constructor <;> decide)
    unfold Erdos634.PgramTiling22Bridge.v1 Erdos634.PgramTiling22Bridge.toZPt
    rw [this]; norm_num
  · have := key PgramTiling22.q2 44 0 0 0 (by constructor <;> decide)
    unfold Erdos634.PgramTiling22Bridge.v2 Erdos634.PgramTiling22Bridge.toZPt
    rw [this]; norm_num
  · have := key PgramTiling22.q3 66 6 0 0 (by constructor <;> decide)
    unfold Erdos634.PgramTiling22Bridge.v3 Erdos634.PgramTiling22Bridge.toZPt
    rw [this]; norm_num
  · have := key PgramTiling22.q4 22 6 0 0 (by constructor <;> decide)
    unfold Erdos634.PgramTiling22Bridge.v4 Erdos634.PgramTiling22Bridge.toZPt
    rw [this]; norm_num

/-- `Δ_2^apex`, `Tiling44Bridge.dissection` translated by `(88, 24√15)`, has vertices at exactly
the hand-derived positions inside `Δ_4`: apex `(176,48√15)`, base corners `(88,24√15)`,
`(264,24√15)`. -/
theorem apex_copy_pts :
    (translateCongruentDissection (mkPt 88 (24 * Real.sqrt 15))
        Erdos634.Tiling44Bridge.dissection).target.pts 0 = mkPt 88 (24 * Real.sqrt 15) ∧
    (translateCongruentDissection (mkPt 88 (24 * Real.sqrt 15))
        Erdos634.Tiling44Bridge.dissection).target.pts 1 = mkPt 264 (24 * Real.sqrt 15) ∧
    (translateCongruentDissection (mkPt 88 (24 * Real.sqrt 15))
        Erdos634.Tiling44Bridge.dissection).target.pts 2 = mkPt 176 (48 * Real.sqrt 15) := by
  have key : ∀ (k : Fin 3) (a b : ℤ),
      (Erdos634.Z15Real.zx (Erdos634.Tiling44Bridge.toZPt
          (![Tiling44.t1 Tiling44.target, Tiling44.t2 Tiling44.target,
            Tiling44.t3 Tiling44.target] k)) = (a, 0) ∧
       Erdos634.Z15Real.zy (Erdos634.Tiling44Bridge.toZPt
          (![Tiling44.t1 Tiling44.target, Tiling44.t2 Tiling44.target,
            Tiling44.t3 Tiling44.target] k)) = (0, b)) →
      (translateCongruentDissection (mkPt 88 (24 * Real.sqrt 15))
        Erdos634.Tiling44Bridge.dissection).target.pts k
        = mkPt (88 + (a:ℝ)) (24 * Real.sqrt 15 + (b:ℝ) * Real.sqrt 15) := by
    intro k a b ⟨hx, hy⟩
    show (transEquiv _).toAffineEquiv (Erdos634.Tiling44Bridge.targetTri.pts k) = _
    rw [Erdos634.Tiling44Bridge.targetTri_pts_eq k, hx, hy]
    show mkPt 88 (24 * Real.sqrt 15) + mkPt (Erdos634.Z15Real.toR (a,0))
      (Erdos634.Z15Real.toR (0,b)) = _
    simp only [Erdos634.Z15Real.toR]; push_cast; rw [mkPt_add]; congr 1 <;> ring
  refine ⟨?_, ?_, ?_⟩
  · have := key 0 0 0 (by constructor <;> decide); rw [this]; norm_num
  · have := key 1 176 0 (by constructor <;> decide); rw [this]; norm_num
  · have := key 2 88 24 (by constructor <;> decide); rw [this]; push_cast; congr 1 <;> ring

/-- The corner triangle, `Tiling44Bridge.dissection` translated by `(176, 0)`, has vertices at
exactly the hand-derived positions inside `Δ_4`: `(176,0)`, `(352,0)`, `(264,24√15)`. -/
theorem corner_copy_pts :
    (translateCongruentDissection (mkPt 176 0)
        Erdos634.Tiling44Bridge.dissection).target.pts 0 = mkPt 176 0 ∧
    (translateCongruentDissection (mkPt 176 0)
        Erdos634.Tiling44Bridge.dissection).target.pts 1 = mkPt 352 0 ∧
    (translateCongruentDissection (mkPt 176 0)
        Erdos634.Tiling44Bridge.dissection).target.pts 2 = mkPt 264 (24 * Real.sqrt 15) := by
  have key : ∀ (k : Fin 3) (a b : ℤ),
      (Erdos634.Z15Real.zx (Erdos634.Tiling44Bridge.toZPt
          (![Tiling44.t1 Tiling44.target, Tiling44.t2 Tiling44.target,
            Tiling44.t3 Tiling44.target] k)) = (a, 0) ∧
       Erdos634.Z15Real.zy (Erdos634.Tiling44Bridge.toZPt
          (![Tiling44.t1 Tiling44.target, Tiling44.t2 Tiling44.target,
            Tiling44.t3 Tiling44.target] k)) = (0, b)) →
      (translateCongruentDissection (mkPt 176 0)
        Erdos634.Tiling44Bridge.dissection).target.pts k
        = mkPt (176 + (a:ℝ)) ((b:ℝ) * Real.sqrt 15) := by
    intro k a b ⟨hx, hy⟩
    show (transEquiv _).toAffineEquiv (Erdos634.Tiling44Bridge.targetTri.pts k) = _
    rw [Erdos634.Tiling44Bridge.targetTri_pts_eq k, hx, hy]
    show mkPt 176 0 + mkPt (Erdos634.Z15Real.toR (a,0)) (Erdos634.Z15Real.toR (0,b)) = _
    simp only [Erdos634.Z15Real.toR]; push_cast; rw [mkPt_add]; congr 1 <;> ring
  refine ⟨?_, ?_, ?_⟩
  · have := key 0 0 0 (by constructor <;> decide); rw [this]; norm_num
  · have := key 1 176 0 (by constructor <;> decide); rw [this]; norm_num
  · have := key 2 88 24 (by constructor <;> decide); rw [this]; push_cast; congr 1 <;> ring
