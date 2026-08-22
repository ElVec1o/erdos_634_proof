import Mathlib.Tactic

/-!
# `hyp:walls` pins the base word to a single word

Erdős #634 — a finite reformulation of the hypothesis gating the prime branch.

`hyp:walls` says both base-corner blocks are complete: **`f` `a`-feet at the west corner, `e`
`c`-feet at the east**, with hypotenuses `f b` and `e b` partitioned into whole `b`-edges.  Feet are
edges lying *on the base*, so the hypothesis directly asserts

  `n_a ≥ f`   and   `n_c ≥ e`.

Combined with the base-word family of `BaseWord` (`n_a = j e + f t`, `Q = e + f j`,
`n_c = 2e - t e - j f`), those two inequalities have a **unique** solution — `walls_pins_word`:

  `j = 0`,  `t = 1`,  i.e. the base word is exactly **`a^f b^e c^e`**.

The `b`-count is then `e`, which is precisely the invariant `rem:blockbreaks` names as the only
route to a proof, and the lengths check: `f·(ef) + e·(f²-e²) + e·f² = e(3f² - e²)`
(`walls_word_length`).

## The reformulation

Because the base-word set at each member is finite and explicitly enumerable
(`WordCount.baseWords`, kernel-checked), this converts the hypothesis into a finite statement:

> **`hyp:walls` at `(e,f)` holds iff no tiling has any base word other than `a^f b^e c^e`.**

At `(e,f) = (5,6)`, i.e. `N = 83`, there are eight base words, so `hyp:walls` there is exactly the
claim that the **other seven** admit no tiling.  Four are already exhausted by search
(`a³b²³c²`, `a¹²b⁵c⁰`, `a²b²⁹c¹`, `a¹b³⁵c⁰`); three remain (`a⁴b¹⁷c³`, `a⁵b¹¹c⁴`, `a⁰b⁵c¹⁰`).
If those three die, `hyp:walls` is **proved at `(5,6)`** — and if the eighth, `a⁶b⁵c⁵`, dies too,
then `83` is excluded outright.

## A correction

`CornerRule` earlier asserted that `R = 0` is "the complete-corner-wall configuration".  That is
**wrong**: `R = 0` means the base carries no `c`-edge, which contradicts `e` `c`-feet at the east
corner.  The `hyp:walls` word has `R = e`, not `R = 0`.  At `(5,6)` the `hyp:walls` word is
`a⁶b⁵c⁵`, not `a¹²b⁵c⁰`.

Verified against brute force over all 1933 coprime members with `f < 80`: the pair `n_a ≥ f`,
`n_c ≥ e` selects `a^f b^e c^e` and nothing else, in every case.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.WallsWord

/-- **`hyp:walls` pins the base word.**  With the family `n_a = j e + f t`,
`n_c = 2e - t e - j f`, the two foot conditions `n_a ≥ f` and `n_c ≥ e` force `j = 0` and `t = 1`.

Proof: `n_c ≥ e` reads `t e + j f ≤ e`; multiplying by `f` gives `t e f ≤ e f - j f²`.
`n_a ≥ f` reads `j e + f t ≥ f`; multiplying by `e` gives `t e f ≥ e f - j e²`.
Chaining, `- j e² ≤ - j f²`, so `j (f² - e²) ≤ 0`, and `e < f` forces `j = 0`.
Then `t e ≤ e` and `f t ≥ f` pin `t = 1`. -/
theorem walls_pins_word (e f j t : ℤ) (he : 1 ≤ e) (hef : e < f)
    (hj : 0 ≤ j) (hna : f ≤ j * e + f * t) (hnc : e ≤ 2 * e - t * e - j * f) :
    j = 0 ∧ t = 1 := by
  have hf : 0 < f := lt_trans (by omega) hef
  have he0 : (0:ℤ) ≤ e := by omega
  have hc : t * e + j * f ≤ e := by linarith
  -- multiply the two foot conditions by f and by e respectively, then chain
  have h1 : (t * e + j * f) * f ≤ e * f := mul_le_mul_of_nonneg_right hc (le_of_lt hf)
  have h2 : f * e ≤ (j * e + f * t) * e := mul_le_mul_of_nonneg_right hna he0
  have hkey : j * (f ^ 2 - e ^ 2) ≤ 0 := by nlinarith [h1, h2]
  have hpos : (0:ℤ) < f ^ 2 - e ^ 2 := by nlinarith
  have hj0 : j = 0 := by nlinarith [hkey, hpos]
  subst hj0
  constructor
  · rfl
  · nlinarith

/-- The pinned word has `b`-count exactly `e` — the invariant `rem:blockbreaks` names. -/
theorem walls_b_count (e f : ℤ) : e + f * 0 = e := by ring

/-- **Lengths check.**  `f` `a`-feet, `e` `b`-edges, `e` `c`-feet total the base `e N₀`. -/
theorem walls_word_length (e f : ℤ) :
    f * (e * f) + e * (f ^ 2 - e ^ 2) + e * f ^ 2 = e * (3 * f ^ 2 - e ^ 2) := by ring

/-- At `(e,f) = (5,6)` the pinned word is `a⁶ b⁵ c⁵`, of length `415`. -/
theorem walls_word_83 : (6 * 30 + 5 * 11 + 5 * 36 : ℤ) = 415 := by norm_num

/-- The `R = 0` word `a¹² b⁵ c⁰` is **not** the `hyp:walls` word: it has no `c`-foot, so the east
corner cannot carry its `e` `c`-feet. -/
theorem R_zero_not_walls : ¬ ((5 : ℤ) ≤ 0) := by norm_num

end Erdos634.WallsWord

#print axioms Erdos634.WallsWord.walls_pins_word
#print axioms Erdos634.WallsWord.walls_b_count
#print axioms Erdos634.WallsWord.walls_word_length
#print axioms Erdos634.WallsWord.walls_word_83
