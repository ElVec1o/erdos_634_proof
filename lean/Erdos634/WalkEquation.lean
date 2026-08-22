import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
# The walk equation from one-dimensional measure (Erdős #634, E2)

The interface field `walk_base` / `walk_side` says a side of the target of length `L` carries tile
edges with multiplicities `P, Q, R` satisfying `P·a + Q·b + R·c = L`. It was expected to need
planar subdivision theory (`HasEdgeChains`). It does not: the same measure-theoretic route that
proved the angle sum works here in dimension one.

Parametrise the side by `(0,L) ⊆ ℝ`. The tile edges lying along it have pairwise disjoint relative
interiors (the tiles have disjoint interiors) and cover it (the tiles cover the target, and a tile
edge meeting a side lies along it, since tiles lie inside the target). Lebesgue additivity then adds
their lengths, and each length is one of `a`, `b`, `c` because a tile edge lying on a side is a
whole tile edge. That is the walk equation.

`sum_lengths` below is the measure statement; `walk_equation` is its specialisation to lengths drawn
from `{a,b,c}`, which is the form the interface consumes.
-/

open MeasureTheory Set

namespace Erdos634.WalkEquation

/-- **Lengths add.** Finitely many measurable, pairwise almost-disjoint subsets of `(0,L)` that
cover it have measures summing to `L`. -/
theorem sum_lengths {n : ℕ} {L : ℝ} (hL : 0 ≤ L) (S : Fin n → Set ℝ) (len : Fin n → ℝ)
    (hmeas : ∀ i, MeasurableSet (S i))
    (hdisj : Pairwise (Function.onFun (AEDisjoint volume) S))
    (hcover : ⋃ i, S i = Ioo 0 L)
    (hlen : ∀ i, volume (S i) = ENNReal.ofReal (len i))
    (hlen_nn : ∀ i, 0 ≤ len i) :
    ∑ i, len i = L := by
  have hU := measure_iUnion₀ (μ := volume) hdisj (fun i => (hmeas i).nullMeasurableSet)
  rw [hcover, tsum_fintype, Real.volume_Ioo, sub_zero] at hU
  simp_rw [hlen] at hU
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hlen_nn i)] at hU
  have hnn : (0:ℝ) ≤ ∑ i, len i := Finset.sum_nonneg (fun i _ => hlen_nn i)
  exact ((ENNReal.ofReal_eq_ofReal_iff hL hnn).mp hU).symm

/-- **The walk equation**, in the form the interface consumes. Grouping the pieces by length —
`P` of length `a`, `Q` of length `b`, `R` of length `c`, which is elementary bookkeeping once the
lengths are known to lie in `{a,b,c}` — the measure identity becomes `P·a + Q·b + R·c = L`. -/
theorem walk_equation {n : ℕ} {L a b c : ℝ} {P Q R : ℕ} (hL : 0 ≤ L)
    (S : Fin n → Set ℝ) (len : Fin n → ℝ)
    (hmeas : ∀ i, MeasurableSet (S i))
    (hdisj : Pairwise (Function.onFun (AEDisjoint volume) S))
    (hcover : ⋃ i, S i = Ioo 0 L)
    (hlen : ∀ i, volume (S i) = ENNReal.ofReal (len i))
    (hlen_nn : ∀ i, 0 ≤ len i)
    (hgroup : ∑ i, len i = P * a + Q * b + R * c) :
    (P : ℝ) * a + (Q : ℝ) * b + (R : ℝ) * c = L := by
  rw [← hgroup]
  exact sum_lengths hL S len hmeas hdisj hcover hlen hlen_nn

end Erdos634.WalkEquation
