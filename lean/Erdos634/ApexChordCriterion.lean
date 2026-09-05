import Erdos634.ExclusionCriterion

/-!
# The apex-chord criterion: the leg exclusion improves from `f ≥ 3e²` to `f ≥ 2e²`

Erdős #634, base-β family at `m = 1`, `N = 3f² − e²`, floor `K·b = f·b`.

`ExclusionCriterion` records that the clearance bound excludes the leg direction exactly when
`e²(3f² − e²) < f³`, i.e. `f ≥ 3e²`.  A second, independent constraint at the **apex** sharpens it.

**The mechanism** (geometric half not formalized — it needs the tile-placement layer).  The apex
angle is `3α`, and `3α = α+α+α` is its *only* fill (`α/π` irrational), so **every tile at the apex
presents `α`**.  The sides at an `α` vertex are `b` and `c`, so the first edge along a leg out of the
apex has length `b` or `c` — both large.  A chord parallel to the other leg, at distance `X` from the
apex, therefore meets that first edge strictly inside it, and the tile carrying that crossing exits
through its `α`-side at distance `X / (2 cos α)`.  Bounding that by the remaining gap gives an
**upper** bound on `X`, while the clearance gives a **lower** one:

> `f⁴/N ≤ X ≤ f e²(2f² − e²)/N`.

The two are incompatible exactly when `e²(2f² − e²) < f³`, and

> **`e²(2f² − e²) < f³  ⟺  2e² ≤ f`.**

`cos_alpha_identity` records the identity the mechanism turns on: `1 + 2cos α = N/f²`, i.e.
`2 cos α = (2f² − e²)/f²`.

**Effect.**  Strictly better than `f ≥ 3e²`.  Among the 13 base-β primes below 250 the old criterion
reached `47, 107, 191` (all `e = 1`); the new one also reaches **`11 (1,2)`** and **`239 (2,9)`** —
the latter being the unique `e ≥ 2` near-miss, whose base and `π−α` directions were already dead.  So
`N = 239` is now reduced to the single direction `π−γ`, the exact tie of Lemma C, which no chord
bound can ever kill.

**It still does not reach `N = 83`** (`f = 6 < 2e² = 50`), nor any of the other seven `e ≥ 2` targets
below 250.  The `e ≥ 2` reach improves from `N ≥ 428` (empty below 250) to `N ≥ 12e⁴ − e²`, which
catches exactly one prime.  Density still zero.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.ApexChordCriterion

/-- **`1 + 2cos α = N/f²`**, the identity the apex-chord bound turns on, with `2cos α = (2f²−e²)/f²`
and `N = 3f² − e²`. -/
theorem cos_alpha_identity {e f : ℚ} (hf : f ≠ 0) :
    1 + (2 * f ^ 2 - e ^ 2) / f ^ 2 = (3 * f ^ 2 - e ^ 2) / f ^ 2 := by
  field_simp; ring

/-- **The apex-chord criterion.**  `e²(2f² − e²) < f³ ⟺ 2e² ≤ f`. -/
theorem apex_exclusion_iff {e f : ℤ} (he : 0 < e) (hef : e < f) :
    e ^ 2 * (2 * f ^ 2 - e ^ 2) < f ^ 3 ↔ 2 * e ^ 2 ≤ f := by
  have hf0 : 0 < f := lt_trans he hef
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    have hstep : e ^ 4 ≤ f ^ 2 * (2 * e ^ 2 - f) := by
      rcases lt_or_ge f (e ^ 2) with hfe | hfe
      · have hA : e ^ 2 < 2 * e ^ 2 - f := by linarith
        have hef2 : e ^ 2 ≤ f ^ 2 := by nlinarith
        have hB : e ^ 2 * e ^ 2 ≤ f ^ 2 * e ^ 2 :=
          mul_le_mul_of_nonneg_right hef2 (sq_nonneg e)
        nlinarith [mul_lt_mul_of_pos_left hA (show (0:ℤ) < f ^ 2 by positivity), hB]
      · have hA : (1:ℤ) ≤ 2 * e ^ 2 - f := by linarith
        nlinarith [mul_le_mul_of_nonneg_left hA (show (0:ℤ) ≤ f ^ 2 by positivity), hfe]
    nlinarith [hstep]
  · intro h
    have hkey : 2 * e ^ 2 * f ^ 2 ≤ f * f ^ 2 := mul_le_mul_of_nonneg_right h (sq_nonneg f)
    nlinarith [hkey, pow_pos he 4]

/-- **The apex criterion is strictly stronger than the clearance criterion.**  `f ≥ 3e² ⟹ f ≥ 2e²`,
so everything the old bound excluded the new one excludes too. -/
theorem apex_stronger {e f : ℤ} (he : 0 < e) (h : 3 * e ^ 2 ≤ f) : 2 * e ^ 2 ≤ f := by nlinarith

/-- **And strictly stronger: `(2,9)` is caught by the new criterion and not the old.**
`f = 9 ≥ 8 = 2e²` but `9 < 12 = 3e²`.  This is `N = 239`. -/
theorem strictly_stronger_at_2_9 : 2 * (2:ℤ) ^ 2 ≤ 9 ∧ ¬ (3 * (2:ℤ) ^ 2 ≤ 9) := by
  constructor <;> decide

/-- **The `(2,9)` incompatibility, exactly.**  `f⁴ = 6561 > 5688 = f e²(2f² − e²)`, so the clearance
lower bound on `X` exceeds the apex upper bound and no admissible chord exists. -/
theorem instance_2_9 : (5688:ℤ) < 6561 := by decide

/-- **`N = 83` is still not reached.**  `(e,f) = (5,6)` has `f = 6 < 50 = 2e²`. -/
theorem not_reached_at_5_6 : ¬ (2 * (5:ℤ) ^ 2 ≤ 6) := by decide

/-- **Reach at `e ≥ 2`.**  `f ≥ 2e²` with `e ≥ 2` forces `N = 3f² − e² ≥ 12e⁴ − e² ≥ 188`. -/
theorem reach_e_ge_two {e f : ℤ} (he : 2 ≤ e) (h : 2 * e ^ 2 ≤ f) :
    188 ≤ 3 * f ^ 2 - e ^ 2 := by
  have he0 : (0:ℤ) < e := by omega
  have hf0 : (0:ℤ) < f := by nlinarith
  have hsq : 4 * e ^ 4 ≤ f ^ 2 := by
    nlinarith [mul_self_le_mul_self (show (0:ℤ) ≤ 2 * e ^ 2 by positivity) h]
  have ht : (4:ℤ) ≤ e ^ 2 := by nlinarith
  nlinarith [hsq, mul_nonneg (show (0:ℤ) ≤ e ^ 2 - 4 by linarith)
    (show (0:ℤ) ≤ 12 * e ^ 2 + 47 by positivity)]

/-! ## The `π−α` direction can never be closed by a clearance argument -/

/-- **Vertex-fan clearance on `π−α` never bites.**  `π−α` is the one direction not parallel to a
target side, so the strip `ClearanceLemma` never applied to it; its extremal chord passes through a
*vertex*, where the fill is forced (apex `3α = α+α+α`, three tiles each showing `α`; each base corner
one tile).  Clearing those known tile interiors gives, on the apex branch, the maximum free chord
`b(f³ − b)/(ef)`.  It falls below the floor `f·b` iff `f³ − f²(1+e) + e² < 0`, i.e.
`f²(f − 1 − e) + e² < 0` — **impossible**, since `f ≥ e+1` makes the first term `≥ 0` and `e² > 0`.

So no clearance or vertex-fan argument can ever exclude `π−α`.  The excess is minimised exactly on
the family `f = e + 1`, where it equals `e²` — and that family contains `N = 83` (`(5,6)`), `11`,
`23`, `59`, `179`.  The direction approaches the floor at rate `1/f` and never reaches it. -/
theorem pi_alpha_fan_never_bites {e f : ℤ} (he : 0 < e) (hef : e < f) :
    0 < f ^ 3 - f ^ 2 * (1 + e) + e ^ 2 := by
  have h1 : 0 ≤ f ^ 2 * (f - 1 - e) := by
    have : 0 ≤ f - 1 - e := by omega
    positivity
  nlinarith [h1, mul_pos he he]

/-- **The excess is exactly `e²` on the family `f = e + 1`** — the tightest it ever gets, and that
family contains `N = 83`. -/
theorem fan_excess_at_f_eq_e_succ (e : ℤ) :
    (e + 1) ^ 3 - (e + 1) ^ 2 * (1 + e) + e ^ 2 = e ^ 2 := by ring

end Erdos634.ApexChordCriterion
