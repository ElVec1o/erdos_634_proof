import Erdos634.ExclusionCriterion

/-!
# The clearance lemma — the step Theorem R actually rests on

Erdős #634.  A six-seat room round surfaced a conflict: one seat reported that the leg direction is
never excluded by the chord/floor bound, against three seats reporting the domain `f ≥ 3e²`.  Both
were right about different bounds, and resolving it exposed the load-bearing step:

* the **raw** maximum chord parallel to a side *is the side itself* (`eN` for the base, `f³` for a
  leg), and `f³ > f·b = Kb` always — so the raw bound excludes **nothing** in the leg direction, at
  any `(e,f)`, `e = 1` included;
* the **clearance-refined** bound does the whole job.

`ROUTE_L23/theoremR.md`'s own `e = 1` table already used it (its `1 − 1/f²` factor is `1 − e/f²`),
but the step was never stated as a lemma and was **not in Lean** — while both Theorem R and its
general-`e` extension R′ rest entirely on it.

> **CLEARANCE LEMMA.**  An essential segment `S` parallel to a side `X` of the target lies at distance
> `≥ h_min = 2·A_tile / c` from `X`.
>
> *Proof.*  `S` is essential, so some tile `T` is supported by `S` on the `X` side; `T` lies inside
> the target, hence inside the closed strip between `line(S)` and `X`, of width `t`.  `T` lays one of
> its sides on `S`, and its altitude to that side is at most the strip width `t`.  That altitude is
> `2·A_tile / ℓ` where `ℓ ∈ {a,b,c}` is the side laid, and `ℓ ≤ c`, so the altitude is at least
> `2·A_tile / c`.  Hence `t ≥ 2·A_tile / c`. ∎

The arithmetic half is what this file certifies: the altitude bound (`altitude_ge_min`), the two
exact clearance ratios `h_min/H = e/f²` (base) and `h_min/d = f/N` (leg), and the refined chord
formulas they produce.  **The geometric half — "a supported tile lies in the strip" — needs the
tile-placement layer and remains a hypothesis**, exactly as elsewhere in this development.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.ClearanceLemma

/-! ## 1. The altitude bound -/

/-- **A triangle's altitude to any side is at least `2·Area / c`**, where `c` is its longest side.
This is why the minimum tile altitude, and not some smaller quantity, is the right clearance. -/
theorem altitude_ge_min {A s c : ℚ} (hA : 0 < A) (hs : 0 < s) (hsc : s ≤ c) :
    2 * A / c ≤ 2 * A / s :=
  div_le_div_of_nonneg_left (by positivity) hs hsc

/-- For the base-β tile the longest side is `c = f²`, so the minimum altitude is `2A/f²`. -/
theorem c_is_longest {e f : ℚ} (he : 0 < e) (hef : e < f) :
    e * f ≤ f ^ 2 ∧ f ^ 2 - e ^ 2 ≤ f ^ 2 := by
  constructor <;> nlinarith

/-! ## 2. The two exact clearance ratios -/

/-- **Base clearance ratio `h_min / H = e / f²`.**  With `A` the tile's area, the target's height
onto its base is `H = 2·(N·A)/(e·N) = 2A/e`, and `h_min = 2A/f²`. -/
theorem clearance_ratio_base {A e f : ℚ} (hA : A ≠ 0) (he : e ≠ 0) (hf : f ≠ 0) :
    (2 * A / f ^ 2) / (2 * A / e) = e / f ^ 2 := by
  field_simp

/-- **Leg clearance ratio `h_min / d = f / N`.**  The distance from a leg to the opposite vertex is
`d = 2·(N·A)/f³`. -/
theorem clearance_ratio_leg {A f N : ℚ} (hA : A ≠ 0) (hf : f ≠ 0) (hN : N ≠ 0) :
    (2 * A / f ^ 2) / (2 * N * A / f ^ 3) = f / N := by
  field_simp

/-! ## 3. The refined chord bounds -/

/-- **Refined base chord.**  `eN·(1 − e/f²) = eN(f² − e)/f²`. -/
theorem refined_base_chord {e f N : ℚ} (hf : f ≠ 0) :
    e * N * (1 - e / f ^ 2) = e * N * (f ^ 2 - e) / f ^ 2 := by
  field_simp

/-- **Refined leg chord.**  `f³·(1 − f/N) = f³(N − f)/N`. -/
theorem refined_leg_chord {f N : ℚ} (hN : N ≠ 0) :
    f ^ 3 * (1 - f / N) = f ^ 3 * (N - f) / N := by
  field_simp

/-! ## 4. Why the raw bound is useless, and the refined one is not -/

/-- **The raw leg chord never falls below the floor**: `f³ > f·b = f(f² − e²)` for every `0 < e < f`.
So the leg direction is excluded by *no* raw length argument, at any `(e,f)` — the conflict the room
surfaced, and the seat that reported it was right. -/
theorem raw_leg_never_excluded {e f : ℚ} (he : 0 < e) (hef : e < f) :
    f * (f ^ 2 - e ^ 2) < f ^ 3 := by
  have hf : 0 < f := lt_trans he hef
  nlinarith [mul_pos hf (mul_pos he he)]

/-- **The refined leg chord does fall below the floor, exactly when `e²N < f³`.**  Over `ℚ`, with
`N > 0` and `f > 0`: `f³(N − f)/N < f(f² − e²) ⟺ e²N < f³`.  This is the criterion
`ExclusionCriterion.leg_exclusion_iff` shows equals `f ≥ 3e²`. -/
theorem refined_leg_exclusion_iff {e f N : ℚ} (hf : 0 < f) (hN : 0 < N)
    (hNdef : N = 3 * f ^ 2 - e ^ 2) :
    f ^ 3 * (N - f) / N < f * (f ^ 2 - e ^ 2) ↔ e ^ 2 * N < f ^ 3 := by
  rw [div_lt_iff₀ hN, hNdef]
  constructor <;> intro h <;> nlinarith [h, hf, sq_nonneg e, sq_nonneg f]

end Erdos634.ClearanceLemma
