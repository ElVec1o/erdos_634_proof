import Erdos634.RegimeSplit

/-!
# The four-direction exclusion is governed by the single criterion `f ≥ 3e²`

Erdős #634, base-β family, `m = 1`, `N = 3f² − e²`, tile `(a,b,c) = (ef, f²−e², f²)`, floor `K·b`
with `K = f`.  Beeson's Theorem 2 puts the essential segment in one of four directions
`{0, β, π−α, π−γ}`; `π−γ` is an exact tie (Lemma C, general in `(e,f)`), and the other three are
excluded by a maximum-chord bound.  Three independent room sessions computed those bounds and agreed:

| direction | excluded iff |
|---|---|
| `β` (leg) | `e²N < f³` |
| `0` (base) | `eN(f²−e) < f³(f²−e²)` |
| `π−α` (thin) | `eN < f³` |

`private/ROUTE_L23/report.md:168` already records the leg equivalence as "P3"; it was **not** in Lean.
What is new, and is the point of this file: **the leg condition implies the other two**, so the whole
four-direction argument has *exactly* P3's domain and the other directions contribute nothing.

> **`e²(3f² − e²) < f³  ⟺  3e² ≤ f`.**

At `e = 1` this is `f ≥ 3`, and all three conditions collapse to `3f² − 1 < f³` — the degeneracy
`e = e² = 1` that made the `e = 1` table show three equal entries.  At `e ≥ 2` they separate, with
the leg strictly binding.  Since `f ≥ 3e²` forces `N = 3f² − e² ≥ 27e⁴ − e² ≥ 428`, **the criterion
reaches no `e ≥ 2` base-β prime below 250** — in particular not `N = 83`.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.ExclusionCriterion

/-- **The governing equivalence.**  `e²(3f² − e²) < f³ ⟺ 3e² ≤ f`. -/
theorem leg_exclusion_iff {e f : ℤ} (he : 0 < e) (hef : e < f) :
    e ^ 2 * (3 * f ^ 2 - e ^ 2) < f ^ 3 ↔ 3 * e ^ 2 ≤ f := by
  have hf0 : 0 < f := lt_trans he hef
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    have hstep : e ^ 4 ≤ f ^ 2 * (3 * e ^ 2 - f) := by
      rcases lt_or_ge f (e ^ 2) with hfe | hfe
      · -- `f < e²`: `3e² − f > 2e²` and `f² > e²`, so `f²(3e²−f) > 2e⁴ ≥ e⁴`
        have hA : 2 * e ^ 2 < 3 * e ^ 2 - f := by linarith
        have hB : e ^ 2 < f ^ 2 := by nlinarith
        nlinarith [mul_lt_mul_of_pos_left hA (show (0:ℤ) < f ^ 2 by positivity), hB]
      · -- `f ≥ e²` and `3e² − f ≥ 1`, so `f²(3e²−f) ≥ f² ≥ e⁴`
        have hA : (1:ℤ) ≤ 3 * e ^ 2 - f := by linarith
        nlinarith [mul_le_mul_of_nonneg_left hA (show (0:ℤ) ≤ f ^ 2 by positivity), hfe]
    nlinarith [hstep]
  · intro h
    have hkey : 3 * e ^ 2 * f ^ 2 ≤ f * f ^ 2 :=
      mul_le_mul_of_nonneg_right h (sq_nonneg f)
    nlinarith [hkey, pow_pos he 4]

/-- **The leg condition implies the `π−α` condition.**  `eN ≤ e²N < f³` since `e ≥ 1`. -/
theorem leg_implies_pi_alpha {e f : ℤ} (he : 0 < e) (hef : e < f)
    (hleg : e ^ 2 * (3 * f ^ 2 - e ^ 2) < f ^ 3) :
    e * (3 * f ^ 2 - e ^ 2) < f ^ 3 := by
  have hN : 0 < 3 * f ^ 2 - e ^ 2 := by nlinarith
  have hee : e ≤ e ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hee hN.le, hleg]

/-- **The leg condition implies the base condition.**  With `f ≥ 3e²`,
`e·N·(f² − e) < f³·(f² − e²)`. -/
theorem leg_implies_base {e f : ℤ} (he : 0 < e) (hef : e < f) (h : 3 * e ^ 2 ≤ f) :
    e * (3 * f ^ 2 - e ^ 2) * (f ^ 2 - e) < f ^ 3 * (f ^ 2 - e ^ 2) := by
  have hf0 : 0 < f := lt_trans he hef
  have hb : 0 < f ^ 2 - e ^ 2 := by nlinarith
  have hN : 0 < 3 * f ^ 2 - e ^ 2 := by nlinarith
  have hleg : e ^ 2 * (3 * f ^ 2 - e ^ 2) < f ^ 3 := (leg_exclusion_iff he hef).mpr h
  -- `e(f²−e) ≤ e²(f²−e²)`, valid for every `e ≥ 1` once `f² ≥ e²+e`
  have hsq : 9 * e ^ 4 ≤ f ^ 2 := by
    nlinarith [mul_self_le_mul_self (show (0:ℤ) ≤ 3 * e ^ 2 by positivity) h]
  have hfe : e ^ 2 + e ≤ f ^ 2 := by nlinarith [hsq, sq_nonneg e]
  -- the difference factors as `e(e−1)(f² − e² − e) ≥ 0`
  have hstep : e * (f ^ 2 - e) ≤ e ^ 2 * (f ^ 2 - e ^ 2) := by
    nlinarith [mul_nonneg (mul_nonneg he.le (show (0:ℤ) ≤ e - 1 by linarith))
      (show (0:ℤ) ≤ f ^ 2 - e ^ 2 - e by linarith)]
  -- multiply through by `N > 0`, then use the leg bound against `b > 0`
  have h1 : e * (3 * f ^ 2 - e ^ 2) * (f ^ 2 - e)
      ≤ e ^ 2 * (3 * f ^ 2 - e ^ 2) * (f ^ 2 - e ^ 2) := by nlinarith [hstep, hN]
  nlinarith [h1, mul_lt_mul_of_pos_right hleg hb]

/-- **All three non-tie directions die together, exactly when `f ≥ 3e²`.** -/
theorem all_three_excluded_iff {e f : ℤ} (he : 0 < e) (hef : e < f) :
    3 * e ^ 2 ≤ f →
      e ^ 2 * (3 * f ^ 2 - e ^ 2) < f ^ 3 ∧
      e * (3 * f ^ 2 - e ^ 2) < f ^ 3 ∧
      e * (3 * f ^ 2 - e ^ 2) * (f ^ 2 - e) < f ^ 3 * (f ^ 2 - e ^ 2) := by
  intro h
  have hleg := (leg_exclusion_iff he hef).mpr h
  exact ⟨hleg, leg_implies_pi_alpha he hef hleg, leg_implies_base he hef h⟩

/-- **At `e = 1` the criterion is `f ≥ 3`**, recovering the recorded `e = 1` condition. -/
theorem at_e_one {f : ℤ} (hf : 1 < f) :
    (1:ℤ) ^ 2 * (3 * f ^ 2 - 1 ^ 2) < f ^ 3 ↔ 3 ≤ f := by
  simpa using leg_exclusion_iff (e := 1) (f := f) one_pos hf

/-- **The criterion cannot reach a small `e ≥ 2` member.**  `f ≥ 3e²` with `e ≥ 2` forces
`N = 3f² − e² ≥ 428`, so no `e ≥ 2` base-β prime below 250 — in particular not `N = 83` — lies in
the argument's domain. -/
theorem no_small_e_ge_two {e f : ℤ} (he : 2 ≤ e) (h : 3 * e ^ 2 ≤ f) :
    428 ≤ 3 * f ^ 2 - e ^ 2 := by
  have he0 : (0:ℤ) < e := by omega
  have hf0 : (0:ℤ) < f := by nlinarith
  have hsq : 9 * e ^ 4 ≤ f ^ 2 := by
    nlinarith [mul_self_le_mul_self (show (0:ℤ) ≤ 3 * e ^ 2 by positivity) h]
  have ht : (4:ℤ) ≤ e ^ 2 := by nlinarith
  nlinarith [hsq, mul_nonneg (show (0:ℤ) ≤ e ^ 2 - 4 by linarith)
    (show (0:ℤ) ≤ 27 * e ^ 2 + 107 by positivity)]

end Erdos634.ExclusionCriterion
