import Erdos634.Dissection

/-!
# Parametrizing a segment by its arc length

Erdős #634, `rem:pingaps` bridge (c)'s instantiation, piece (2) (scoped in `PAPER_MAP.md`,
2026-09-04): a wall segment's Hausdorff measure needs to be read off as a **parameter-interval
length**, not just a total distance, so that `Contiguity.lean`'s abstract 1-D interval facts
(`sortedPositions`, `no_gap_between`, ...) can be applied to a real `Dissection.lineChain`.

This file supplies the first, most elementary piece of that bridge: two points on the same affine
line, parametrized by `AffineMap.lineMap`, are at distance equal to the parameter gap times the
line's own length. Everything downstream (matching a chain edge's trace to a parameter interval)
composes this with `MeasureTheory.hausdorffMeasure_segment`.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.LineParam

open Erdos634.Geometry

/-- **Distance scales with the parameter gap along a line.** For any two parameters `s`, `t`,
the points `lineMap u v s` and `lineMap u v t` are at distance `|s - t| * dist u v`. -/
theorem dist_lineMap_lineMap (u v : Plane) (s t : ℝ) :
    dist (AffineMap.lineMap u v s) (AffineMap.lineMap u v t) = |s - t| * dist u v := by
  simp only [AffineMap.lineMap_apply, vadd_eq_add]
  rw [dist_eq_norm]
  have hexpand : s • (v -ᵥ u) + u - (t • (v -ᵥ u) + u) = (s - t) • (v -ᵥ u) := by
    simp only [vsub_eq_sub]
    module
  rw [hexpand, norm_smul, Real.norm_eq_abs, vsub_eq_sub, ← dist_eq_norm, dist_comm v u]

/-- **The parametrization is injective when `u ≠ v`.** -/
theorem lineMap_injective_of_ne {u v : Plane} (huv : u ≠ v) :
    Function.Injective (AffineMap.lineMap u v : ℝ → Plane) := by
  intro s t hst
  have hd := dist_lineMap_lineMap u v s t
  rw [hst, dist_self] at hd
  have hdne : dist u v ≠ 0 := dist_ne_zero.mpr huv
  have : |s - t| = 0 := by
    by_contra hne
    exact hdne (by
      rcases (mul_eq_zero.mp hd.symm) with h1 | h2
      · exact absurd h1 hne
      · exact h2)
  have := abs_eq_zero.mp this
  linarith

end Erdos634.LineParam
