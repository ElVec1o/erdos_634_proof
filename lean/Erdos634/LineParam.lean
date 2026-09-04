import Erdos634.Dissection
import Erdos634.ChordTraceReal
import Erdos634.Contiguity
import Erdos634.WallChain

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

open Erdos634.ChordTraceReal Erdos634.Contiguity in
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



/-! ## Composing two `lineMap`s: a sub-parametrization is itself a `lineMap`

Needed for the final assembly: two chain edges' parameter *sub*-intervals, each itself given by a
`lineMap u v`, must be compared as plain real intervals (`Ioo`/`Icc`) to invoke `Contiguity`'s
1-D lemmas. This identity converts between the two pictures. -/

/-- **`lineMap` composed with a sub-parametrization stays on the same line.** Reparametrizing
`lineMap (lineMap u v p) (lineMap u v q)` — the `lineMap` between two points of the `u v` line —
by `t` lands on `lineMap u v (p + t*(q-p))`, the point at the corresponding combined parameter. -/
theorem lineMap_lineMap_comb (u v : Plane) (p q t : ℝ) :
    AffineMap.lineMap (AffineMap.lineMap u v p) (AffineMap.lineMap u v q) t
      = AffineMap.lineMap u v (p + t * (q - p)) := by
  simp only [AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub, smul_eq_mul]
  have : v - u = v - u := rfl
  match u, v with
  | u, v => module

/-- **The open segment between two `lineMap` points is the image of the open real interval.** -/
theorem openSegment_lineMap_eq_image_Ioo (u v : Plane) {p q : ℝ} (hpq : p < q) :
    openSegment ℝ (AffineMap.lineMap u v p) (AffineMap.lineMap u v q)
      = (AffineMap.lineMap u v) '' Ioo p q := by
  rw [openSegment_eq_image_lineMap]
  ext y
  simp only [Set.mem_image, Set.mem_Ioo]
  constructor
  · rintro ⟨t, ⟨ht0, ht1⟩, hty⟩
    refine ⟨p + t * (q - p), ⟨by nlinarith, by nlinarith⟩, ?_⟩
    rw [← lineMap_lineMap_comb, hty]
  · rintro ⟨s, ⟨hsp, hsq⟩, hsy⟩
    refine ⟨(s - p) / (q - p), ⟨by
      apply div_pos <;> linarith, by
      rw [div_lt_one (by linarith)]; linarith⟩, ?_⟩
    rw [lineMap_lineMap_comb]
    have hne : q - p ≠ 0 := by linarith
    have hst : p + (s - p) / (q - p) * (q - p) = s := by
      rw [div_mul_cancel₀ _ hne]; ring
    rw [hst]
    exact hsy


/-! ## Final assembly piece: subsingleton trace-intersection gives disjoint parameter intervals

`Dissection.sameside_edges_subsingleton` gives, for two distinct chain edges, that their (full)
edges meet in at most one point — hence so do their traces on the wall segment. Converted through
`openSegment_lineMap_eq_image_Ioo` and `lineMap_injective_of_ne`, this is exactly
`Contiguity.distinct_left_endpoints`'s hypothesis. -/

/-- **A subsingleton segment-intersection forces disjoint open parameter intervals.** If the
segments `[lineMap u v p1, lineMap u v q1]` and `[lineMap u v p2, lineMap u v q2]` meet in at most
one point, then `Ioo p1 q1` and `Ioo p2 q2` are disjoint. -/
theorem Ioo_disjoint_of_subsingleton_inter (u v : Plane) (huv : u ≠ v) {p1 q1 p2 q2 : ℝ}
    (hsub : (segment ℝ (AffineMap.lineMap u v p1) (AffineMap.lineMap u v q1) ∩
        segment ℝ (AffineMap.lineMap u v p2) (AffineMap.lineMap u v q2)).Subsingleton) :
    Ioo p1 q1 ∩ Ioo p2 q2 = ∅ := by
  by_contra hne
  have hne' : (Ioo p1 q1 ∩ Ioo p2 q2).Nonempty := Set.nonempty_iff_ne_empty.mpr hne
  rw [Set.Ioo_inter_Ioo, Set.nonempty_Ioo] at hne'
  obtain ⟨x, hx1, hx2⟩ := exists_between hne'
  obtain ⟨y, hy1, hy2⟩ := exists_between hx2
  have hxy : x ≠ y := hy1.ne
  have hxmem : x ∈ Ioo p1 q1 ∩ Ioo p2 q2 := by
    rw [Set.Ioo_inter_Ioo]; exact ⟨hx1, hx2⟩
  have hymem : y ∈ Ioo p1 q1 ∩ Ioo p2 q2 := by
    rw [Set.Ioo_inter_Ioo]; exact ⟨hx1.trans hy1, hy2⟩
  have hp1q1 : p1 < q1 := hxmem.1.1.trans hxmem.1.2
  have hp2q2 : p2 < q2 := hxmem.2.1.trans hxmem.2.2
  have hxseg1 : AffineMap.lineMap u v x ∈
      segment ℝ (AffineMap.lineMap u v p1) (AffineMap.lineMap u v q1) :=
    openSegment_subset_segment ℝ _ _
      ((openSegment_lineMap_eq_image_Ioo u v hp1q1).symm ▸ ⟨x, hxmem.1, rfl⟩)
  have hyseg1 : AffineMap.lineMap u v y ∈
      segment ℝ (AffineMap.lineMap u v p1) (AffineMap.lineMap u v q1) :=
    openSegment_subset_segment ℝ _ _
      ((openSegment_lineMap_eq_image_Ioo u v hp1q1).symm ▸ ⟨y, hymem.1, rfl⟩)
  have hxseg2 : AffineMap.lineMap u v x ∈
      segment ℝ (AffineMap.lineMap u v p2) (AffineMap.lineMap u v q2) :=
    openSegment_subset_segment ℝ _ _
      ((openSegment_lineMap_eq_image_Ioo u v hp2q2).symm ▸ ⟨x, hxmem.2, rfl⟩)
  have hyseg2 : AffineMap.lineMap u v y ∈
      segment ℝ (AffineMap.lineMap u v p2) (AffineMap.lineMap u v q2) :=
    openSegment_subset_segment ℝ _ _
      ((openSegment_lineMap_eq_image_Ioo u v hp2q2).symm ▸ ⟨y, hymem.2, rfl⟩)
  have hxy' : AffineMap.lineMap u v x ≠ AffineMap.lineMap u v y :=
    fun h => hxy (lineMap_injective_of_ne huv h)
  exact hxy' (hsub ⟨hxseg1, hxseg2⟩ ⟨hyseg1, hyseg2⟩)




/-! ## The coverage step: essentially-disjoint intervals summing to the whole cover it exactly

The last piece of `rem:pingaps` bridge (c)'s instantiation, scoped last tick. `wall_partition` gives
the sum identity; `Ioo_disjoint_of_subsingleton_inter` gives essential disjointness. What was
missing is the general 1-D fact connecting them: essentially-disjoint closed sub-intervals of
`[a,b]` whose lengths sum to `b-a` cover `[a,b]` exactly — no separate "coverage hypothesis" is
needed, since `MeasureTheory.measure_biUnion_finset₀` computes the union's measure from the sum
*unconditionally*, given only essential disjointness. -/

open MeasureTheory in
/-- **Essentially-disjoint closed sub-intervals summing to the whole length cover it exactly.**
Given `lo i ≤ hi i ⊆ [a,b]` for each `i` in a finite index set, pairwise essentially disjoint
(`Subsingleton` overlap), and `∑ i, (hi i - lo i) = b - a`, the union of the closed intervals is
all of `Icc a b`. -/
theorem iUnion_Icc_eq_of_sum_eq_length {ι : Type*} (a b : ℝ) (hab : a < b) (s : Finset ι)
    (lo hi : ι → ℝ) (hle : ∀ i ∈ s, lo i ≤ hi i)
    (hsub : ∀ i ∈ s, Icc (lo i) (hi i) ⊆ Icc a b)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (Icc (lo i) (hi i) ∩ Icc (lo j) (hi j)).Subsingleton)
    (hsum : ∑ i ∈ s, (hi i - lo i) = b - a) :
    (⋃ i ∈ s, Icc (lo i) (hi i)) = Icc a b := by
  classical
  have hmeas : ∀ i ∈ s, volume (Icc (lo i) (hi i)) = ENNReal.ofReal (hi i - lo i) := fun i hi' => by
    rw [Real.volume_Icc]
  have hadd : volume (⋃ i ∈ s, Icc (lo i) (hi i)) = ∑ i ∈ s, volume (Icc (lo i) (hi i)) :=
    measure_biUnion_finset₀
      (fun i h1 j h2 hij => (hdisj i h1 j h2 hij).finite.measure_zero volume)
      (fun i _ => measurableSet_Icc.nullMeasurableSet)
  have hsum' : ∑ i ∈ s, volume (Icc (lo i) (hi i)) = ENNReal.ofReal (b - a) := by
    rw [Finset.sum_congr rfl hmeas, ← ENNReal.ofReal_sum_of_nonneg (fun i hi' => by linarith [hle i hi']),
      hsum]
  have hvol : volume (⋃ i ∈ s, Icc (lo i) (hi i)) = volume (Icc a b) := by
    rw [hadd, hsum', Real.volume_Icc]
  have hclosed : IsClosed (⋃ i ∈ s, Icc (lo i) (hi i)) :=
    Set.Finite.isClosed_biUnion s.finite_toSet (fun i _ => isClosed_Icc)
  have hsub' : (⋃ i ∈ s, Icc (lo i) (hi i)) ⊆ Icc a b := Set.iUnion₂_subset hsub
  exact Erdos634.Contiguity.closed_full_measure_eq hab _ hclosed hsub' hvol



/-! ## The `Icc` form of the injectivity step, matching `iUnion_Icc_eq_of_sum_eq_length`'s hypothesis -/

/-- **A subsingleton segment-intersection forces a subsingleton `Icc`-intersection.** The closed
form of `Ioo_disjoint_of_subsingleton_inter`, matching `iUnion_Icc_eq_of_sum_eq_length`'s `hdisj`
directly. -/
theorem mem_segment_lineMap_of_mem_Icc (u v : Plane) {p q x : ℝ} (hpq : p ≤ q)
    (hx : x ∈ Icc p q) :
    AffineMap.lineMap u v x ∈ segment ℝ (AffineMap.lineMap u v p) (AffineMap.lineMap u v q) := by
  rcases eq_or_lt_of_le hpq with heq | hlt
  · have : x = p := le_antisymm (heq ▸ hx.2) hx.1
    rw [this, heq]; exact left_mem_segment ℝ _ _
  · set t := (x - p) / (q - p) with htdef
    have ht0 : 0 ≤ t := div_nonneg (by linarith [hx.1]) (by linarith)
    have ht1 : t ≤ 1 := by
      rw [htdef, div_le_one (by linarith)]; linarith [hx.2]
    have hne : q - p ≠ 0 := by linarith
    have htx : p + t * (q - p) = x := by
      rw [htdef, div_mul_cancel₀ _ hne]; ring
    rw [segment_eq_image_lineMap]
    refine ⟨t, ⟨ht0, ht1⟩, ?_⟩
    rw [lineMap_lineMap_comb, htx]

theorem Icc_subsingleton_of_subsingleton_inter (u v : Plane) (huv : u ≠ v) {p1 q1 p2 q2 : ℝ}
    (hpq1 : p1 ≤ q1) (hpq2 : p2 ≤ q2)
    (hsub : (segment ℝ (AffineMap.lineMap u v p1) (AffineMap.lineMap u v q1) ∩
        segment ℝ (AffineMap.lineMap u v p2) (AffineMap.lineMap u v q2)).Subsingleton) :
    (Icc p1 q1 ∩ Icc p2 q2).Subsingleton := by
  intro x hx y hy
  have hx1 := mem_segment_lineMap_of_mem_Icc u v hpq1 hx.1
  have hx2 := mem_segment_lineMap_of_mem_Icc u v hpq2 hx.2
  have hy1 := mem_segment_lineMap_of_mem_Icc u v hpq1 hy.1
  have hy2 := mem_segment_lineMap_of_mem_Icc u v hpq2 hy.2
  have heq := hsub ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
  exact lineMap_injective_of_ne huv heq



/-! ## Final assembly: instantiating the toolkit against a real `Dissection.lineChain`

The last step. Given the standard wall setup (`Dissection.wall_partition`'s own hypotheses), this
produces the actual `hi - lo` sum identity and pairwise-subsingleton facts
`iUnion_Icc_eq_of_sum_eq_length` needs, for the wall's own `lineChain`. -/

open Erdos634.Geometry Erdos634.Contiguity in
/-- **Every chain edge's trace is convex, compact, and on the wall line** — the three
`wall_trace_param_or_empty` hypotheses, discharged for a real `Dissection.lineChain` edge. -/
theorem lineChain_trace_convex_compact_online {N : ℕ} (D : Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) {e : Fin N × Fin 3} (he : e ∈ D.lineChain f c) :
    Convex ℝ ((D.tile e.1).edge e.2) ∧ IsCompact ((D.tile e.1).edge e.2) ∧
      ∀ x ∈ (D.tile e.1).edge e.2, f x = c :=
  ⟨convex_segment _ _, isCompact_segment _ _, D.lineChain_edge_subset he⟩






open scoped Classical in
/-- **The raw (unsorted) parameters of a chain edge's trace**, extracted from
`wall_trace_param_or_empty` via `Classical.choice`: `(0, 0)` if the trace is empty, else `(tp, tq)`
with `tp`, `tq` **not** sorted — sorting is done at call sites via `min`/`max`, kept out of the
definition itself to keep this lemma's own proof a plain `unfold`/`dif_pos` (a redesign after last
tick's tactic loop trying to reconstruct a sorted pair). -/
noncomputable def edgeParam {N : ℕ} (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ)
    (u v : Plane) (e : Fin N × Fin 3) : ℝ × ℝ :=
  if h : ∃ tp ∈ Icc (0:ℝ) 1, ∃ tq ∈ Icc (0:ℝ) 1,
      (D.tile e.1).edge e.2 ∩ segment ℝ u v =
        segment ℝ (AffineMap.lineMap u v tp) (AffineMap.lineMap u v tq) ∧
      (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
          ((D.tile e.1).edge e.2 ∩ segment ℝ u v)
        = ENNReal.ofReal (|tp - tq| * dist u v)
  then (h.choose, h.choose_spec.2.choose)
  else (0, 0)

open Erdos634.Geometry in
/-- **`edgeParam`'s correctness**, raw and unsorted. Either the trace is empty and `edgeParam = (0,0)`,
or `edgeParam = (tp, tq)` with `tp, tq ∈ [0,1]`, trace `= segment (lineMap tp) (lineMap tq)`, and
measure `= ofReal (|tp - tq| * dist u v)`. -/
theorem edgeParam_spec {N : ℕ} (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    (u v : Plane) (huv : u ≠ v) {e : Fin N × Fin 3} (he : e ∈ D.lineChain f c)
    (hu : f u = c) (hv : f v = c) :
    (D.tile e.1).edge e.2 ∩ segment ℝ u v = ∅ ∧ edgeParam D f c u v e = (0, 0) ∨
    (edgeParam D f c u v e).1 ∈ Icc (0:ℝ) 1 ∧ (edgeParam D f c u v e).2 ∈ Icc (0:ℝ) 1 ∧
      (D.tile e.1).edge e.2 ∩ segment ℝ u v =
        segment ℝ (AffineMap.lineMap u v (edgeParam D f c u v e).1)
          (AffineMap.lineMap u v (edgeParam D f c u v e).2) ∧
      (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
          ((D.tile e.1).edge e.2 ∩ segment ℝ u v)
        = ENNReal.ofReal (|(edgeParam D f c u v e).1 - (edgeParam D f c u v e).2| * dist u v) := by
  obtain ⟨hconv, hcpt, hline⟩ := lineChain_trace_convex_compact_online D f c he
  rcases wall_trace_param_or_empty hconv hcpt f hf c hline u v huv hu hv
    with hempty | ⟨tp, htp, tq, htq, heq, hmeas⟩
  · left
    have hnex : ¬ ∃ tp ∈ Icc (0:ℝ) 1, ∃ tq ∈ Icc (0:ℝ) 1,
        (D.tile e.1).edge e.2 ∩ segment ℝ u v =
          segment ℝ (AffineMap.lineMap u v tp) (AffineMap.lineMap u v tq) ∧
        (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
            ((D.tile e.1).edge e.2 ∩ segment ℝ u v)
          = ENNReal.ofReal (|tp - tq| * dist u v) := by
      rintro ⟨tp, -, tq, -, heq', -⟩
      rw [hempty] at heq'
      exact Set.notMem_empty (AffineMap.lineMap u v tp)
        (heq' ▸ left_mem_segment ℝ (AffineMap.lineMap u v tp) (AffineMap.lineMap u v tq))
    exact ⟨hempty, by unfold edgeParam; rw [dif_neg hnex]⟩
  · right
    have hex : ∃ tp' ∈ Icc (0:ℝ) 1, ∃ tq' ∈ Icc (0:ℝ) 1,
        (D.tile e.1).edge e.2 ∩ segment ℝ u v =
          segment ℝ (AffineMap.lineMap u v tp') (AffineMap.lineMap u v tq') ∧
        (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
            ((D.tile e.1).edge e.2 ∩ segment ℝ u v)
          = ENNReal.ofReal (|tp' - tq'| * dist u v) := ⟨tp, htp, tq, htq, heq, hmeas⟩
    have hparam : edgeParam D f c u v e = (hex.choose, hex.choose_spec.2.choose) := by
      unfold edgeParam; rw [dif_pos hex]
    rw [hparam]
    exact ⟨hex.choose_spec.1, hex.choose_spec.2.choose_spec.1,
      hex.choose_spec.2.choose_spec.2.1, hex.choose_spec.2.choose_spec.2.2⟩



/-- **Two distinct chain edges' sorted parameter intervals meet in at most one point.** Assembles
`edgeParam_spec` (either edge could have an empty trace, in which case its interval is the
degenerate `{0}`, trivially subsingleton against anything) with `Dissection.sameside_edges_subsingleton`
and `Icc_subsingleton_of_subsingleton_inter` for the case both traces are real segments. -/
theorem edgeParam_Icc_subsingleton {N : ℕ} (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0)
    (c : ℝ) (u v : Plane) (huv : u ≠ v) {e₁ e₂ : Fin N × Fin 3}
    (he₁ : e₁ ∈ D.lineChain f c) (he₂ : e₂ ∈ D.lineChain f c) (hne : e₁ ≠ e₂)
    (hu : f u = c) (hv : f v = c)
    (hle₁ : ∀ y ∈ (D.tile e₁.1).carrier, f y ≤ c) (hle₂ : ∀ y ∈ (D.tile e₂.1).carrier, f y ≤ c) :
    (Icc (min (edgeParam D f c u v e₁).1 (edgeParam D f c u v e₁).2)
        (max (edgeParam D f c u v e₁).1 (edgeParam D f c u v e₁).2) ∩
      Icc (min (edgeParam D f c u v e₂).1 (edgeParam D f c u v e₂).2)
        (max (edgeParam D f c u v e₂).1 (edgeParam D f c u v e₂).2)).Subsingleton := by
  rcases edgeParam_spec D f hf c u v huv he₁ hu hv with ⟨-, hz₁⟩ | ⟨hb1, hb2, heq1, -⟩
  · rw [hz₁]; simp only [min_self, max_self]
    exact fun x hx y hy => (le_antisymm hx.1.2 hx.1.1).trans (le_antisymm hy.1.2 hy.1.1).symm
  · rcases edgeParam_spec D f hf c u v huv he₂ hu hv with ⟨-, hz₂⟩ | ⟨hc1, hc2, heq2, -⟩
    · rw [hz₂]; simp only [min_self, max_self]
      exact fun x hx y hy => (le_antisymm hx.2.2 hx.2.1).trans (le_antisymm hy.2.2 hy.2.1).symm
    · have hedgesub := D.sameside_edges_subsingleton f c hf hne hle₁ hle₂
        (D.lineChain_edge_subset he₁) (D.lineChain_edge_subset he₂)
      have htracesub : ((D.tile e₁.1).edge e₁.2 ∩ segment ℝ u v ∩
          ((D.tile e₂.1).edge e₂.2 ∩ segment ℝ u v)).Subsingleton :=
        hedgesub.anti (by intro x hx; exact ⟨hx.1.1, hx.2.1⟩)
      rw [heq1, heq2] at htracesub
      have hsymm1 : segment ℝ (AffineMap.lineMap u v (edgeParam D f c u v e₁).1)
          (AffineMap.lineMap u v (edgeParam D f c u v e₁).2) =
          segment ℝ (AffineMap.lineMap u v (min (edgeParam D f c u v e₁).1 (edgeParam D f c u v e₁).2))
            (AffineMap.lineMap u v (max (edgeParam D f c u v e₁).1 (edgeParam D f c u v e₁).2)) := by
        rcases le_total (edgeParam D f c u v e₁).1 (edgeParam D f c u v e₁).2 with h1 | h1
        · rw [min_eq_left h1, max_eq_right h1]
        · rw [min_eq_right h1, max_eq_left h1]; exact _root_.segment_symm (𝕜 := ℝ) _ _
      have hsymm2 : segment ℝ (AffineMap.lineMap u v (edgeParam D f c u v e₂).1)
          (AffineMap.lineMap u v (edgeParam D f c u v e₂).2) =
          segment ℝ (AffineMap.lineMap u v (min (edgeParam D f c u v e₂).1 (edgeParam D f c u v e₂).2))
            (AffineMap.lineMap u v (max (edgeParam D f c u v e₂).1 (edgeParam D f c u v e₂).2)) := by
        rcases le_total (edgeParam D f c u v e₂).1 (edgeParam D f c u v e₂).2 with h2 | h2
        · rw [min_eq_left h2, max_eq_right h2]
        · rw [min_eq_right h2, max_eq_left h2]; exact _root_.segment_symm (𝕜 := ℝ) _ _
      rw [hsymm1, hsymm2] at htracesub
      exact Icc_subsingleton_of_subsingleton_inter u v huv min_le_max min_le_max htracesub



/-- **The final sum identity**: converting `Dissection.wall_partition`'s `ENNReal` measure sum into
the real-number `hsum` `iUnion_Icc_eq_of_sum_eq_length` needs, via `edgeParam_spec`'s per-edge
measure identity. -/
theorem lineChain_param_sum {N : ℕ} (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0)
    (c : ℝ) (u v : Plane) (huv : u ≠ v)
    (hS : segment ℝ u v ⊆ {y | f y = c})
    (hint : openSegment ℝ u v ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ u v, ∀ i, y ∉ interior (D.tile i).carrier) :
    ∑ e ∈ D.lineChain f c,
        (max (edgeParam D f c u v e).1 (edgeParam D f c u v e).2
          - min (edgeParam D f c u v e).1 (edgeParam D f c u v e).2)
      = 1 := by
  have hu : f u = c := hS (left_mem_segment ℝ u v)
  have hv : f v = c := hS (right_mem_segment ℝ u v)
  have hpart := D.wall_partition f c hf huv hS hint hwall
  have hstep : ∀ e ∈ D.lineChain f c,
      (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
          ((D.tile e.1).edge e.2 ∩ segment ℝ u v)
        = ENNReal.ofReal
          ((max (edgeParam D f c u v e).1 (edgeParam D f c u v e).2
            - min (edgeParam D f c u v e).1 (edgeParam D f c u v e).2) * dist u v) := by
    intro e he
    rcases edgeParam_spec D f hf c u v huv he hu hv with ⟨hempty', hz⟩ | ⟨-, -, -, hmeas⟩
    · rw [hz, hempty']
      simp
    · rw [hmeas]
      congr 2
      rcases le_total (edgeParam D f c u v e).1 (edgeParam D f c u v e).2 with h | h
      · rw [min_eq_left h, max_eq_right h, abs_of_nonpos (by linarith), neg_sub]
      · rw [min_eq_right h, max_eq_left h, abs_of_nonneg (by linarith)]
  rw [Finset.sum_congr rfl hstep] at hpart
  rw [← ENNReal.ofReal_sum_of_nonneg (fun e _ => by
    have := min_le_max (a := (edgeParam D f c u v e).1) (b := (edgeParam D f c u v e).2)
    positivity)] at hpart
  rw [MeasureTheory.hausdorffMeasure_segment, edist_dist] at hpart
  rw [← Finset.sum_mul] at hpart
  have hdpos : 0 < dist u v := dist_pos.mpr huv
  have hkey : (∑ e ∈ D.lineChain f c,
      (max (edgeParam D f c u v e).1 (edgeParam D f c u v e).2
        - min (edgeParam D f c u v e).1 (edgeParam D f c u v e).2)) * dist u v
      = 1 * dist u v := by
    have hnn : (0:ℝ) ≤ ∑ e ∈ D.lineChain f c,
        (max (edgeParam D f c u v e).1 (edgeParam D f c u v e).2
          - min (edgeParam D f c u v e).1 (edgeParam D f c u v e).2) :=
      Finset.sum_nonneg (fun e _ => sub_nonneg.mpr min_le_max)
    have := (ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)).mp hpart
    simpa using this
  have hfin := mul_right_cancel₀ hdpos.ne' hkey
  linarith [hfin]



/-- **The wall segment's parametrization is covered exactly by the chain's sorted parameter
intervals.** Composes `lineChain_param_sum`, `edgeParam_spec`'s bounds, and
`edgeParam_Icc_subsingleton` into `iUnion_Icc_eq_of_sum_eq_length`. -/
theorem lineChain_covers_Icc {N : ℕ} (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0)
    (c : ℝ) (u v : Plane) (huv : u ≠ v)
    (hS : segment ℝ u v ⊆ {y | f y = c})
    (hint : openSegment ℝ u v ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ u v, ∀ i, y ∉ interior (D.tile i).carrier)
    (hle : ∀ e ∈ D.lineChain f c, ∀ y ∈ (D.tile e.1).carrier, f y ≤ c) :
    (⋃ e ∈ D.lineChain f c,
        Icc (min (edgeParam D f c u v e).1 (edgeParam D f c u v e).2)
          (max (edgeParam D f c u v e).1 (edgeParam D f c u v e).2))
      = Icc (0:ℝ) 1 := by
  have hu : f u = c := hS (left_mem_segment ℝ u v)
  have hv : f v = c := hS (right_mem_segment ℝ u v)
  refine iUnion_Icc_eq_of_sum_eq_length 0 1 zero_lt_one (D.lineChain f c)
    (fun e => min (edgeParam D f c u v e).1 (edgeParam D f c u v e).2)
    (fun e => max (edgeParam D f c u v e).1 (edgeParam D f c u v e).2)
    (fun e _ => min_le_max) (fun e he => ?_) (fun e₁ he₁ e₂ he₂ hne =>
      edgeParam_Icc_subsingleton D f hf c u v huv he₁ he₂ hne hu hv
        (hle e₁ he₁) (hle e₂ he₂))
    (by rw [sub_zero]; exact lineChain_param_sum D f hf c u v huv hS hint hwall)
  dsimp only
  rcases edgeParam_spec D f hf c u v huv he hu hv with ⟨-, hz⟩ | ⟨hb1, hb2, -, -⟩
  · rw [hz]; intro x hx; simp only [min_self, max_self, Icc_self, Set.mem_singleton_iff] at hx
    subst hx; exact ⟨le_refl 0, zero_le_one⟩
  · intro x hx
    exact ⟨(le_min hb1.1 hb2.1).trans hx.1, hx.2.trans (max_le hb1.2 hb2.2)⟩



/-! ## Composing into `sortedPositions`/`orderedChain` — and a genuine subtlety found

`sortedPositions`/`mem_sortedPositions`/`sortedPositions_sorted` are unconditional (no injectivity
needed) — they apply directly to `D.lineChain f c` with `lo := fun e => min (edgeParam ...).1
(edgeParam ...).2`. What is **not** automatic is `sortedPositions_length`/`orderedChain_length`
(one list entry per chain edge): that needs `Set.InjOn lo (D.lineChain f c)`, which **fails in
general** — every chain edge whose trace is empty (it doesn't touch this particular wall segment)
defaults to `lo = 0` under `edgeParam`'s convention, so any two such edges collide. The right fix is
restricting to the sub-`Finset` of edges with nonempty trace before asking for one-entry-per-edge;
that restriction, and its own injectivity proof, is not attempted here. -/

/-- **The sorted list of a real wall's chain positions exists, is sorted, and contains every chain
edge's position** — unconditionally, no injectivity needed. This is as far as `sortedPositions`
composes without addressing the empty-trace collision above. -/
theorem lineChain_sortedPositions_valid {N : ℕ} (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ)
    (c : ℝ) (u v : Plane) {e : Fin N × Fin 3} (he : e ∈ D.lineChain f c) :
    (min (edgeParam D f c u v e).1 (edgeParam D f c u v e).2) ∈
      Erdos634.Contiguity.sortedPositions (D.lineChain f c)
        (fun e => min (edgeParam D f c u v e).1 (edgeParam D f c u v e).2) ∧
    (Erdos634.Contiguity.sortedPositions (D.lineChain f c)
      (fun e => min (edgeParam D f c u v e).1 (edgeParam D f c u v e).2)).SortedLT :=
  ⟨Erdos634.Contiguity.mem_sortedPositions (D.lineChain f c) _ he,
    Erdos634.Contiguity.sortedPositions_sorted (D.lineChain f c) _⟩

end Erdos634.LineParam
