import Erdos634.RunForcing

/-!
# `T_mid` untileable — the arithmetic and the march actually composed

Erdős #634.  `MidTriangleGeneral` proved two things that did **not** talk to each other:
`base_partition` (the base is `e` whole `b`-sides) and `midTriangle_untileable_general` (the march
contradiction, over abstract `L R : ℕ → ℝ` with the tile count `n` taken as given).  A room seat
correctly flagged that the main theorem never invokes the arithmetic lemma, so the file was a pair of
disconnected halves rather than one argument.  This file composes them: the number of base tiles is
**derived** from the edge-partition equation, not assumed.

It also takes the sharper scale hypothesis.  The kill does not need `m = 1`; it needs

> **`m·e < f`** — the inner scale below the modulus.

That is what `RunForcing.run_all_b` actually requires (`k = m·e < f`), and it is the honest acceptance
condition: the three certified controls `N = 44, 99, 176` are `(e,f) = (1,2)` at `m = 2,3,4`, so
`m·e = 2,3,4 ≥ 2 = f` and the kill correctly does **not** reach them.  `m = 1` implies `m·e = e < f`
always, so the prime case is covered. (Verified exhaustively: the all-`b` forcing holds iff `m·e < f`,
no mismatches over coprime `(e,f)` with `f ≤ 13`, `m ≤ 7`.)

Axiom-clean; no `sorry`.
-/

namespace Erdos634.MidTriangleComposed

open Erdos634.MidTriangleGeneral Erdos634.RunForcing

/-- **`T_mid` is untileable — composed.**  The base of `T_mid` has length `(m·e)·b` and is covered by
tile edges with multiplicities `(u,v,w)`; `run_all_b` forces `u = w = 0` and `v = m·e`, so there are
exactly `m·e` base tiles, and the march then contradicts the corner at `D'`.

The geometric inputs remain hypotheses (`hends`, `hjunction`, `hD`, `hD'`) — they need the
tile-placement layer this development does not have — but the *tile count* is now derived, so the
arithmetic is load-bearing rather than decorative. -/
theorem midTriangle_untileable_composed
    (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : γ = 2 * α + β)
    (hrel : 3 * α + 2 * β = Real.pi)
    (e f m : ℤ) (he : 0 < e) (hef : e < f) (hcop : IsCoprime e f)
    (hm : 0 < m) (hscale : m * e < f)
    -- the base of `T_mid`, of length `(m·e)·b`, covered by whole tile edges
    (u v w : ℤ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hpart : u * (e * f) + v * (f ^ 2 - e ^ 2) + w * f ^ 2 = (m * e) * (f ^ 2 - e ^ 2))
    -- the march data, indexed by the number of base tiles
    (L R : ℕ → ℝ)
    (hends : ∀ j < v.toNat, (L j = α ∧ R j = γ) ∨ (L j = γ ∧ R j = α))
    (hD : L 0 ≤ α + β)
    (hjunction : ∀ j, j + 1 < v.toNat → R j + L (j + 1) ≤ Real.pi)
    (hD' : R (v.toNat - 1) ≤ α + β) : False := by
  have hme : 0 < m * e := mul_pos hm he
  -- the arithmetic does the work: `v = m·e`, and in particular `v > 0`
  obtain ⟨-, hveq, -⟩ := run_all_b he hef hcop hme hscale hu hv hw hpart
  have hvpos : 0 < v.toNat := by
    rw [hveq]; omega
  exact midTriangle_untileable_general α β γ hα hβ hγ hrel v.toNat hvpos L R hends hD hjunction hD'

/-- **The kill's acceptance condition is `m·e < f`, and the certified controls fail it.**
`N = 44, 99, 176` are `(e,f) = (1,2)` at `m = 2,3,4`; each has `m·e ≥ f`, so this argument does not
touch them.  Recorded as a theorem so the negative control is checked, not asserted. -/
theorem controls_not_reached : ¬ ((2:ℤ) * 1 < 2) ∧ ¬ ((3:ℤ) * 1 < 2) ∧ ¬ ((4:ℤ) * 1 < 2) :=
  ⟨by omega, by omega, by omega⟩

/-- **The prime case is covered**: `m = 1` gives `m·e = e < f` always. -/
theorem prime_case_covered {e f : ℤ} (hef : e < f) : 1 * e < f := by omega

end Erdos634.MidTriangleComposed
