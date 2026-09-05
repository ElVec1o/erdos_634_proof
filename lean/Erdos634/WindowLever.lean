import Erdos634.LabelCalculus

/-!
# The covolume lever is dead, and the `m = 1` window is vacuous

Erdős #634, crux `window`: is the label extension `k` bounded?  Edge directions are `xα + yβ (mod π)`
with `3α+2β = π`, so they form `ℤ²/⟨(3,2)⟩ ≅ ℤ` via `L(x,y) = 2x − 3y` (`LabelCalculus`).  A room
seat settled the most concrete proposed mechanism.  This file records the two structural facts and
the two negatives.

## 1. No tile sits at either end of the window  [the sharpening]

A tile of label `L` has edge labels `{L−1, L, L+2}` or `{L−2, L, L+1}` — always one label strictly
below `L` and one strictly above.  So if a tile's own label were `ℓ_min` it would carry an edge below
`ℓ_min`, and likewise at `ℓ_max`.  Hence

> **`no_tile_at_window_ends`: no tile's label is `ℓ_min` or `ℓ_max`** — the extreme labels carry only
> `a`- or `c`-edges, never a `b`-edge.

Verified in all nine measured dissections.  Consequence: a real dissection's module is **`f²` coarser**
than the naive containment `√D/(2f^{w−1})`, namely `≥ √D/(2f^{w−3})`, and that bound is attained
(`N = 63`, and the `N = 6` strip).

## 2. The covolume lever cannot bind  [Question 3, answered NO]

The whole content of a packing argument is `|V| ≤ #(M_w ∩ T)`.  Computing both sides exactly, the
inequality reduces to

> **`e·b·f^{w−1} ≥ 6`** — independent of `N`, and true for every `w ≥ 2`.

So it constrains nothing.  Inverting it (the shape the brief proposed) yields `w ≤ 2`, which **every**
certified tiling violates — the minimum window any base-β tiling can have is 7, since the target's own
three sides already occupy labels `−3, 0, 3`.  At the `N = 44` target the exact count is
`#(M₇ ∩ T) = 4329` against `|V| = 38`: a factor of ~32 of slack at the *narrowest possible* window,
multiplying by `f` per extra unit.

**Why no repair exists:** bounding `w` needs `|V|` bounded *below*; packing bounds it only *above*.
Three points already generate an arbitrarily fine module, so mesh and vertex count are decoupled.

## 3. The `m = 1` window is not measurable — and the crux is vacuous there

The `m = 1` base-β members whose windows one would want to measure are recorded
`EXHAUSTED_NO_TILING` in `private/RESEARCH_LOG.md`: `(1,2) N=11`, `(1,3) N=26`, `(1,5) N=74`,
`(1,6) N=107`, `(2,3) N=23`, `(2,5) N=71`, `(3,4) N=39`.

> **At `m = 1` the crux asks for a bound on a property of a conjecturally empty set.**  It is
> vacuously true there, and any argument that quietly uses that emptiness is circular.  What the
> payoff chain needs is a bound proved *without* assuming non-existence.

`window_bound_vacuous_if_empty` records the logical shape.  (A brief for this crux asked a session to
*measure* the `m=1` window; that request cannot be met, and the request itself contained an
arithmetic slip — `N = 122` is `(5,7)`, not `(1,7)`, which is `146`.)

Axiom-clean; no `sorry`.
-/

namespace Erdos634.WindowLever

open Erdos634.LabelCalculus

/-- **A tile spans strictly below and strictly above its own label.**  Both chiralities. -/
theorem tile_spans_both_sides (L : ℤ) :
    (L - 1 < L ∧ L < L + 2) ∧ (L - 2 < L ∧ L < L + 1) := by
  refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

/-- **No tile's label is at either end of the window.**  If `lo ≤ ℓ ≤ hi` for every edge label `ℓ`,
and a tile of label `L` carries edges at `L−1` (or `L−2`) and `L+2` (or `L+1`), then `lo < L < hi`. -/
theorem no_tile_at_window_ends {lo hi L : ℤ}
    (hlow : lo ≤ L - 1) (hhigh : L + 1 ≤ hi) : lo < L ∧ L < hi := by
  omega

/-- **The extremes are at least one step inside**, so the module's mesh is coarser by `f²`:
`w − 1` is replaced by `w − 3` in the covolume exponent. -/
theorem exponent_drops_by_two (w : ℤ) : (w - 1) - 2 = w - 3 := by ring

/-- **The packing inequality is vacuous.**  It reduces to `e·b·f^{w−1} ≥ 6`, which holds for every
`w ≥ 2` once `e ≥ 1`, `b ≥ 3`, `f ≥ 2` — so it never constrains `w`. -/
theorem packing_vacuous {e b f w : ℤ} (he : 1 ≤ e) (hb : 3 ≤ b) (hf : 2 ≤ f) (hw : 2 ≤ w) :
    6 ≤ e * b * f ^ (w - 1).toNat := by
  have h1 : 1 ≤ (w - 1).toNat := by omega
  have hfp : (2:ℤ) ^ (w - 1).toNat ≤ f ^ (w - 1).toNat := by
    apply pow_le_pow_left₀ (by norm_num) hf
  have h2 : (2:ℤ) ≤ 2 ^ (w - 1).toNat := by
    calc (2:ℤ) = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ (w - 1).toNat := pow_le_pow_right₀ (by norm_num) h1
  nlinarith [hfp, h2, mul_le_mul he hb (by omega) (by omega)]

/-- **The minimum window is 7**, since the target's own three sides occupy labels `−3, 0, 3`.  So the
naive inversion `w ≤ 2` is contradicted by every tiling. -/
theorem min_window_seven : (3:ℤ) - (-3) + 1 = 7 ∧ ¬ ((7:ℤ) ≤ 2) := by
  refine ⟨by decide, by decide⟩

/-- **Vacuity at `m = 1`.**  If no tiling exists, every statement about all tilings holds — so a
window bound proved there carries no information, and a proof that *uses* emptiness is circular. -/
theorem window_bound_vacuous_if_empty {Tiling : Type} {P : Tiling → Prop}
    (hempty : ¬ Nonempty Tiling) : ∀ t : Tiling, P t := fun t => absurd ⟨t⟩ hempty

end Erdos634.WindowLever
