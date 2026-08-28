import Mathlib.Tactic
import Erdos634.BaseBetaE1

/-!
# The fan kill: the arithmetic half of the (4,2) refutation, parametric in `f`

Erdős #634, `e = 1` hole.  The engine's refutation of the `(bp,cp) = (4,2)` base word was mined
from coordinate traces (research log, 2026-08-26) and is, in its entire growing part, one
mechanism: at the base junction between the word's first `a` and its `c`, the west corner tile
shows `γ` and the `c`-tile shows `α`, leaving a wedge of exactly `π - γ - α = β`; a fan of
`α`-tiles fills it step by step, and after `k = ⌊β/α⌋` steps the remainder `β - kα` is a corner
smaller than every tile angle.  Measured `k = 4, 6, 7, 9` at `f = 4..7` — exactly `⌊β/α⌋` — with
the binary chirality choices not affecting the angle, which is why every branch dies identically.

This file proves the **arithmetic half**, for every `f` at once:

* `wedge_is_beta`      — the wedge is exactly `β`.
* `no_exact_fan`       — no number of `α`s ever equals `β`: `kα = β` would make `α = π/(3+2k)`,
  against `tile_alpha_irrational` (which is general in `(e,f)`).
* `fan_remainder`      — with `k = ⌊β/α⌋₊`, the remainder satisfies `0 < β - kα < α`.
* `fan_kill`           — nothing whose angle is at least the minimal tile angle fits in it.

## The two named geometric hypotheses (open; interface discipline)

The assembly consumes two statements not proved here, carried as hypotheses:

* **(FanForcing)** every tile meeting the junction from inside the wedge has a vertex there and
  presents exactly `α` — the traces show the alternatives dying in the constant-size side cases
  (the `f`-independent prune counts `12, 2, 7`), and that finite case analysis is the open half;
* **(MinAngle)** `α` is the minimal tile angle at `e = 1` (numerically: `sin(α/2) = 1/(2f) ≤ 1/8`
  for `f ≥ 4`, so `α < π/5 < β < γ`; not yet formalized).

**Scope caveat.**  This kills the `(4,2)`-type words, where the letter after the initial `a` is the
`c`.  The `(3,2)` word (the `b` adjacent to the `c`) produces a radically different tree — `3.2`
million nodes without termination at `f = 8` — and is NOT covered.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.FanKill

open Real

/-- **The wedge at the `a|c` junction is exactly `β`.**  `π - γ - α = β` from the branch relations
`γ = 2α + β` and `3α + 2β = π`. -/
theorem wedge_is_beta (a b g p : ℝ) (hg : g = 2*a + b) (hp : p = 3*a + 2*b) :
    p - g - a = b := by rw [hg, hp]; ring

/-- **No number of `α`s equals `β`.**  `kα = β` forces `(3 + 2k)α = π`, i.e. `α` a rational
multiple of `π`, against the irrationality supplied by `BaseBetaE1.tile_alpha_irrational`. -/
theorem no_exact_fan (a b : ℝ) (hsum : 3*a + 2*b = π)
    (hirr : ¬ ∃ r : ℚ, a = (r : ℝ) * π) (k : ℕ) : (k : ℝ) * a ≠ b := by
  intro h
  refine hirr ⟨(1 : ℚ) / (3 + 2 * k), ?_⟩
  have hk : (3 + 2 * (k : ℝ)) * a = π := by linarith
  have hpos : (0 : ℝ) < 3 + 2 * (k : ℝ) := by positivity
  push_cast
  field_simp
  linarith [hk]

/-- **The fan remainder is trapped strictly between `0` and `α`.**  `k = ⌊β/α⌋₊` gives
`kα ≤ β < (k+1)α`, and equality on the left is excluded by `no_exact_fan`. -/
theorem fan_remainder (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hsum : 3*a + 2*b = π) (hirr : ¬ ∃ r : ℚ, a = (r : ℝ) * π) :
    0 < b - (⌊b / a⌋₊ : ℝ) * a ∧ b - (⌊b / a⌋₊ : ℝ) * a < a := by
  have hdiv : (0 : ℝ) ≤ b / a := le_of_lt (div_pos hb ha)
  have hle : (⌊b / a⌋₊ : ℝ) ≤ b / a := Nat.floor_le hdiv
  have hlt : b / a < (⌊b / a⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have h1 : (⌊b / a⌋₊ : ℝ) * a ≤ b := by
    have := mul_le_mul_of_nonneg_right hle (le_of_lt ha)
    rwa [div_mul_cancel₀ b (ne_of_gt ha)] at this
  have h2 : b < ((⌊b / a⌋₊ : ℝ) + 1) * a := by
    have := mul_lt_mul_of_pos_right hlt ha
    rwa [div_mul_cancel₀ b (ne_of_gt ha)] at this
  have hne : (⌊b / a⌋₊ : ℝ) * a ≠ b := no_exact_fan a b hsum hirr _
  constructor
  · rcases lt_or_eq_of_le h1 with h | h
    · linarith
    · exact absurd h hne
  · nlinarith [h2]

/-- **Nothing fits in the remainder.**  Any angle at least the minimal tile angle `a` exceeds the
remainder, and an edge through the corner would contribute `π > a`. -/
theorem fan_kill (a r θ : ℝ) (hr : r < a) (hθ : a ≤ θ) : ¬ θ ≤ r := by
  intro h; linarith

/-- **Assembled.**  Under (FanForcing) — the fan advances by exactly `α` per step — and (MinAngle),
the `(4,2)` junction dies at step `⌊β/α⌋₊` for every `f`: the wedge is `β`, the fan never closes it
exactly, and the final remainder admits no tile.  The two hypotheses are the open geometric half. -/
theorem fan_dies (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hsum : 3*a + 2*b = π) (hirr : ¬ ∃ r : ℚ, a = (r : ℝ) * π)
    (θ : ℝ) (hθ : a ≤ θ) :
    ¬ θ ≤ b - (⌊b / a⌋₊ : ℝ) * a :=
  fan_kill a _ θ (fan_remainder a b ha hb hsum hirr).2 hθ

/-! ## First fixed cases of (FanForcing), and the chain's kill arithmetic

The traces hand us the case analysis; these are its first arithmetic entries.

* The **overrun identity**: an edge of length `c` laid along a ray of length `b` overruns by
  exactly `c - b = 1`.
* A leftover run of length `1` is a **semigroup gap**: `1 < f = min generator`, so no tile edge and
  no sum of tile edges covers it.  This is the mechanism killing the side branches of the base-word
  march (the `P2` leaves), and the reason the roof-tile alternatives at the pin die. -/

/-- **The overrun is exactly one.**  `c - b = f² - (f² - 1) = 1`, for every `f`. -/
theorem overrun_is_one (f : ℤ) : f ^ 2 - (f ^ 2 - 1) = 1 := by ring

/-- **A run of length `1` is a semigroup gap** for `⟨f, f²-1, f²⟩` once `f ≥ 2`: any nonzero
nonnegative combination is at least `f > 1`. -/
theorem one_is_gap (f x y z : ℕ) (hf : 2 ≤ f)
    (h : x * f + y * (f ^ 2 - 1) + z * f ^ 2 = 1) : False := by
  have hf2 : 4 ≤ f ^ 2 := by nlinarith
  have hb : 3 ≤ f ^ 2 - 1 := by omega
  rcases Nat.eq_zero_or_pos x with hx | hx
  · rcases Nat.eq_zero_or_pos y with hy | hy
    · rcases Nat.eq_zero_or_pos z with hz | hz
      · simp [hx, hy, hz] at h
      · have : f ^ 2 ≤ z * f ^ 2 := Nat.le_mul_of_pos_left _ hz
        omega
    · have : f ^ 2 - 1 ≤ y * (f ^ 2 - 1) := Nat.le_mul_of_pos_left _ hy
      omega
  · have : f ≤ x * f := Nat.le_mul_of_pos_left _ hx
    omega

end Erdos634.FanKill
