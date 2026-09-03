import Erdos634.WbtwChain

/-!
# Betweenness from `p` is exactly the real-distance order

Erdős #634. `wbtw_trichotomy_of_wbtw` / `_antisymm_` / `_trans_` show `Wbtw ℝ p · ·` is a genuine
total order on points weakly between `p` and `q`. This identifies that order concretely: it is
*exactly* the order of `dist p ·`. This is what lets a `Finset` of chord points — straddler trace
endpoints, in the intended application — be sorted using `ℝ`'s own decidable linear order (via
`dist p ·`) instead of building bespoke order instances on `Plane` directly.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.ChordTraceReal

namespace Erdos634.ChordTraceReal

/-- **Betweenness from `p` is exactly the real-distance order.** For `x, y` both weakly between `p`
and `q`, `Wbtw ℝ p x y` holds iff `dist p x ≤ dist p y`. -/
theorem wbtw_iff_dist_le_of_wbtw {p q x y : Plane} (hx : Wbtw ℝ p x q) (hy : Wbtw ℝ p y q) :
    Wbtw ℝ p x y ↔ dist p x ≤ dist p y := by
  constructor
  · intro h
    have heq : dist p x + dist x y = dist p y := dist_add_dist_eq_iff.mpr h
    linarith [dist_nonneg (x := x) (y := y)]
  · intro hle
    rcases wbtw_trichotomy_of_wbtw hx hy with h | h
    · exact h
    · have heq : dist p y + dist y x = dist p x := dist_add_dist_eq_iff.mpr h
      have h0 : dist y x = 0 := by linarith [dist_nonneg (x := y) (y := x)]
      have hyx : y = x := dist_eq_zero.mp h0
      rw [hyx]
      exact wbtw_self_right ℝ p x

end Erdos634.ChordTraceReal
