import Erdos634.Dissection
import Erdos634.ChordTraceReal

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

open Erdos634.Geometry Set

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



/-! ## Piece (2b): Hausdorff measure of a sub-segment, in parameter units -/

/-- **A parametrized sub-segment's Hausdorff measure is its parameter-gap length.** Combines
`hausdorffMeasure_segment` with `dist_lineMap_lineMap`: the segment between two points of the line
`u v`, given by parameters `p`, `q`, has `μH¹` equal to `|p - q| * dist u v` (as an `ENNReal`, via
`ENNReal.ofReal`). -/
theorem hausdorffMeasure_segment_lineMap (u v : Plane) (p q : ℝ) :
    (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
        (segment ℝ (AffineMap.lineMap u v p) (AffineMap.lineMap u v q))
      = ENNReal.ofReal (|p - q| * dist u v) := by
  rw [MeasureTheory.hausdorffMeasure_segment, edist_dist, dist_lineMap_lineMap]



/-! ## Piece (3): a wall-segment trace is a parametrized sub-segment, with known measure

Composes `ChordTraceReal.isSegment_of_convex_inter_hyperplane` (any convex compact subset of a line
is a segment) with `segment_eq_image_lineMap` (a segment's own points are `lineMap`-images) and
`hausdorffMeasure_segment_lineMap`: the trace of *any* set lying on the wall line and intersected
with the wall segment — in particular a chain edge's trace — is itself `segment (lineMap u v tp)
(lineMap u v tq)` for parameters `tp, tq ∈ [0,1]`, with Hausdorff measure `|tp - tq| * dist u v`. -/

open Erdos634.ChordTraceReal in
/-- **A wall-segment trace is a parametrized sub-segment.** If `S` is convex, compact, and lies on
the line `{f = c}` through `u ≠ v` (with `S` nonempty, witnessed by `x0`), then `S = segment
(lineMap u v tp) (lineMap u v tq)` for some `tp, tq ∈ [0,1]`, and its Hausdorff measure is
`|tp - tq| * dist u v`. -/
theorem trace_eq_param_segment {S : Set Plane} (hconv : Convex ℝ S) (hcpt : IsCompact S)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ) (hSf : ∀ x ∈ S, f x = c)
    (x0 : Plane) (hx0 : x0 ∈ S) (u v : Plane) (huv : u ≠ v)
    (hSsub : S ⊆ segment ℝ u v) :
    ∃ tp ∈ Icc (0:ℝ) 1, ∃ tq ∈ Icc (0:ℝ) 1,
      S = segment ℝ (AffineMap.lineMap u v tp) (AffineMap.lineMap u v tq) ∧
      (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) S
        = ENNReal.ofReal (|tp - tq| * dist u v) := by
  obtain ⟨p, q, hpS, hqS, hSpq⟩ :=
    isSegment_of_convex_inter_hyperplane hconv hcpt f hf c hSf x0 hx0
  have hpseg : p ∈ segment ℝ u v := hSsub hpS
  have hqseg : q ∈ segment ℝ u v := hSsub hqS
  rw [segment_eq_image_lineMap] at hpseg hqseg
  obtain ⟨tp, htp, hptp⟩ := hpseg
  obtain ⟨tq, htq, hqtq⟩ := hqseg
  refine ⟨tp, htp, tq, htq, ?_, ?_⟩
  · rw [hSpq, ← hptp, ← hqtq]
  · rw [hSpq, ← hptp, ← hqtq, hausdorffMeasure_segment_lineMap]



/-! ## Applying the bridge to a real wall-segment trace -/

/-- **A segment is compact.** Same pattern as `Tri.isClosed_edge`'s proof. -/
theorem isCompact_segment (x y : Plane) : IsCompact (segment ℝ x y) := by
  rw [segment_eq_image]
  exact isCompact_Icc.image (by fun_prop)

/-- **The trace of any set on the wall line, intersected with the wall segment, is a parametrized
sub-segment or empty.** Applies `trace_eq_param_segment` to `S = E ∩ segment u v`, given only that
`E` is convex, compact, and lies on the line `{f = c}` (true in particular for a tile edge, via
`Tri.edge`'s own convexity/compactness and `Dissection.lineChain_edge_subset`). -/
theorem wall_trace_param_or_empty {E : Set Plane} (hEconv : Convex ℝ E) (hEcpt : IsCompact E)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ) (hEf : ∀ x ∈ E, f x = c)
    (u v : Plane) (huv : u ≠ v) (hu : f u = c) (hv : f v = c) :
    E ∩ segment ℝ u v = ∅ ∨
    ∃ tp ∈ Icc (0:ℝ) 1, ∃ tq ∈ Icc (0:ℝ) 1,
      E ∩ segment ℝ u v = segment ℝ (AffineMap.lineMap u v tp) (AffineMap.lineMap u v tq) ∧
      (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) (E ∩ segment ℝ u v)
        = ENNReal.ofReal (|tp - tq| * dist u v) := by
  by_cases hne : (E ∩ segment ℝ u v).Nonempty
  · right
    obtain ⟨x0, hx0⟩ := hne
    have hconv : Convex ℝ (E ∩ segment ℝ u v) := hEconv.inter (convex_segment u v)
    have hcpt : IsCompact (E ∩ segment ℝ u v) := hEcpt.inter_right (isCompact_segment u v).isClosed
    have hSf : ∀ x ∈ E ∩ segment ℝ u v, f x = c := fun x hx => hEf x hx.1
    exact trace_eq_param_segment hconv hcpt f hf c hSf x0 hx0 u v huv Set.inter_subset_right
  · left
    exact Set.not_nonempty_iff_eq_empty.mp hne

end Erdos634.LineParam
