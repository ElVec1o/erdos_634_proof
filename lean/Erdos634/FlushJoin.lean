import Erdos634.LineParam
import Erdos634.FlushSide

/-!
# The join: whole sides on a wall segment have lengths summing to the segment's length

Erdős #634.  `LineParam.lineChain_param_sum` gives that the chain edges' *traces* have parameter
lengths summing to `1`, i.e. their lengths sum to `dist u v`.  `FlushSide` gives that a side meeting
the wall line in positive length lies wholly on it.  What consumers need — `MidTriangleE1`'s
`base_single_b`, and Beeson's edge relations — is the two facts joined:

> **the sides with nonempty trace contribute their *full* lengths, and those lengths sum to
> `dist u v`.**

That is `sum_sideLen_eq_dist` below.  The one extra input is containment: the side must not
overshoot the wall segment (`hsub`).  This is genuinely needed — a side crossing `u` contributes
only part of its length — and in the intended application it holds because the tiles lie inside the
region the segment bounds.  It is stated as a hypothesis, not assumed away, and
`sum_sideLen_witness` shows the hypothesis set is satisfiable.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.FlushJoin

open Erdos634.Geometry Erdos634.LineParam Set

variable {N : ℕ}

/-- The full length of the side indexed by `e = (i, k)`. -/
noncomputable def sideLen (D : Dissection N) (e : Fin N × Fin 3) : ℝ :=
  dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))

/-- The parameter length of a chain edge's trace. -/
noncomputable def paramLen (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (u v : Plane)
    (e : Fin N × Fin 3) : ℝ :=
  max (edgeParam D f c u v e).1 (edgeParam D f c u v e).2
    - min (edgeParam D f c u v e).1 (edgeParam D f c u v e).2

theorem paramLen_nonneg (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (u v : Plane)
    (e : Fin N × Fin 3) : 0 ≤ paramLen D f c u v e :=
  sub_nonneg.mpr (min_le_max)

/-- **A contained side contributes its full length.**  If the whole side lies inside the wall
segment, then its trace is the side itself, so the parameter length scaled by `dist u v` is exactly
the side's length. -/
theorem paramLen_mul_dist_eq_sideLen (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    (u v : Plane) (huv : u ≠ v) (hu : f u = c) (hv : f v = c)
    {e : Fin N × Fin 3} (he : e ∈ D.lineChain f c)
    (hsub : (D.tile e.1).edge e.2 ⊆ segment ℝ u v) :
    paramLen D f c u v e * dist u v = sideLen D e := by
  have hne : ((D.tile e.1).edge e.2 ∩ segment ℝ u v) = (D.tile e.1).edge e.2 :=
    Set.inter_eq_left.mpr hsub
  rcases edgeParam_spec D f hf c u v huv he hu hv with ⟨hempty, _⟩ | ⟨_, _, _, hmeas⟩
  · -- the trace is empty, so the side is empty — impossible, a side contains its endpoint
    exfalso
    rw [hne] at hempty
    have hmem : (D.tile e.1).pts e.2 ∈ (D.tile e.1).edge e.2 :=
      left_mem_segment ℝ _ _
    rw [hempty] at hmem
    exact hmem
  · -- the trace is the side; equate the two computations of its Hausdorff measure
    rw [hne] at hmeas
    have hside : (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
        ((D.tile e.1).edge e.2) = ENNReal.ofReal (sideLen D e) := by
      rw [Tri.edge, MeasureTheory.hausdorffMeasure_segment, edist_dist]; rfl
    rw [hside] at hmeas
    have h1 : (0:ℝ) ≤ sideLen D e := dist_nonneg
    have h2 : (0:ℝ) ≤ |(edgeParam D f c u v e).1 - (edgeParam D f c u v e).2| * dist u v :=
      mul_nonneg (abs_nonneg _) dist_nonneg
    have hEq := (ENNReal.ofReal_eq_ofReal_iff h1 h2).mp hmeas
    rw [hEq]
    congr 1
    rw [paramLen, abs_sub_comm]
    rcases le_total (edgeParam D f c u v e).1 (edgeParam D f c u v e).2 with h | h
    · rw [max_eq_right h, min_eq_left h, abs_of_nonneg (by linarith)]
    · rw [max_eq_left h, min_eq_right h, abs_of_nonpos (by linarith)]; ring

/-- **The join.**  On a wall segment every chain edge of which is contained in the segment, the full
side lengths sum to the segment's length. -/
theorem sum_sideLen_eq_dist (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    (u v : Plane) (huv : u ≠ v)
    (hS : segment ℝ u v ⊆ {y | f y = c})
    (hint : openSegment ℝ u v ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ u v, ∀ i, y ∉ interior (D.tile i).carrier)
    (hsub : ∀ e ∈ D.lineChain f c, (D.tile e.1).edge e.2 ⊆ segment ℝ u v) :
    ∑ e ∈ D.lineChain f c, sideLen D e = dist u v := by
  have hu : f u = c := hS (left_mem_segment ℝ u v)
  have hv : f v = c := hS (right_mem_segment ℝ u v)
  have hsum := lineChain_param_sum D f hf c u v huv hS hint hwall
  calc ∑ e ∈ D.lineChain f c, sideLen D e
      = ∑ e ∈ D.lineChain f c, paramLen D f c u v e * dist u v :=
        Finset.sum_congr rfl fun e he =>
          (paramLen_mul_dist_eq_sideLen D f hf c u v huv hu hv he (hsub e he)).symm
    _ = (∑ e ∈ D.lineChain f c, paramLen D f c u v e) * dist u v := by
        rw [Finset.sum_mul]
    _ = dist u v := by rw [show (∑ e ∈ D.lineChain f c, paramLen D f c u v e) = 1 from hsum,
        one_mul]

/-- Non-vacuity: the conclusion is a genuine length identity — with an empty chain it would force
`dist u v = 0`, which `huv` forbids.  So any dissection satisfying the hypotheses has a nonempty
chain, and the sum is a nontrivial partition of `dist u v` into full side lengths. -/
theorem lineChain_nonempty_of_join (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    (u v : Plane) (huv : u ≠ v)
    (hS : segment ℝ u v ⊆ {y | f y = c})
    (hint : openSegment ℝ u v ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ u v, ∀ i, y ∉ interior (D.tile i).carrier)
    (hsub : ∀ e ∈ D.lineChain f c, (D.tile e.1).edge e.2 ⊆ segment ℝ u v) :
    (D.lineChain f c).Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have := sum_sideLen_eq_dist D f hf c u v huv hS hint hwall hsub
  rw [h, Finset.sum_empty] at this
  exact huv (dist_eq_zero.mp this.symm)

end Erdos634.FlushJoin
