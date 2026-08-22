import Mathlib.Tactic

/-!
# What the tile's own arithmetic explains

Erdős #634 — four identities that collapse several apparent coincidences into one picture.

## 1. The "golden ratio" is the tile's side ordering

`WallNeighbour` and `CLayerRigid` both turned on the sign of `f⁴ - 3e²f² + e⁴`, reported each time
as a golden-ratio threshold `e/f` vs `1/φ` and left unexplained.  It factors:

  `f⁴ - 3e²f² + e⁴ = (f² - e²)² - (ef)² = b² - a²`   (`golden_is_b_sq_minus_a_sq`)

So every one of those thresholds asks a single question — **is `b` shorter than `a`?** — and
`b < a ⟺ f² - ef - e² < 0 ⟺ f/e < φ`.  The golden ratio is not a coincidence in the geometry; it
is where the tile's second and third sides cross.  Verified over all coprime members with `f < 200`.

## 2. The three base words are one identity plus one trade

  `N₀ = b + 2c`  (`N0_eq_b_add_two_c`)   and   `f·a = e·c`  (`fa_eq_ec`)

The base at `m = 1` has length `e N₀ = e·b + 2e·c`, so it is "`e` copies of `b`, `2e` of `c`"; and
`f` `a`-edges have exactly the length of `e` `c`-edges, so an `a^f` block and a `c^e` block are
interchangeable.  Trading them gives the three `j = 0` words and nothing else:

| trades | word | |
|---|---|---|
| 0 | `b^e c^{2e}` | |
| 1 | `a^f b^e c^e` | **the `hyp:walls` word** |
| 2 | `a^{2f} b^e` | killed by `GammaCount` (no `c`-edge) |

So above `f = 2e` the branch is "zero or one trade", and `hyp:walls` is exactly **one trade**.

## 3. `c` is unsplittable exactly when `e ≥ 2`

`a` and `b` are unsplittable at every member.  For `c`: reducing `x a + y b = c` mod `f` gives
`f ∣ y e²`, hence `f ∣ y`; and `y ≥ f` is impossible on size, since it would force `b ≤ f`, i.e.
`e² ≥ f² - f`, against `e ≤ f - 1`.  So `y = 0`, `x e f = f²`, and `e ∣ f` forces `e = 1`
(`c_splits_only_at_e_one`).  Then `c = a^f`, which is the trade at `e = 1`.

> **At `e = 1` the `c`-edge can be subdivided; at `e ≥ 2` no tile edge can be subdivided at all.**

## 4. Which inverts the difficulty

Every forcing argument here runs on unsplittability, so `e ≥ 2` is the **more rigid** regime, not the
harder one.  Concretely: the counterexample that killed my "a base break consumes the `c`" argument
placed an `a`-edge strictly inside a `b`-edge, which needs `a < b`.  In the `b < a` regime nothing
is shorter than `b`, so no edge can sit strictly inside a `b`-edge and that escape is unavailable.

`e = 1` lies entirely in the `a < b` regime — which is why it resisted, and why the companion needs
the strip-and-column machinery precisely there.  `N = 83`'s member `(5,6)` has `b = 11 < a = 30`
and lies in the other regime.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.TileArithmetic

/-- **The golden quartic is `b² - a²`.** -/
theorem golden_is_b_sq_minus_a_sq (e f : ℤ) :
    f ^ 4 - 3 * e ^ 2 * f ^ 2 + e ^ 4 = (f ^ 2 - e ^ 2) ^ 2 - (e * f) ^ 2 := by ring

/-- and it factors through the Fibonacci form `f² - ef - e²` of `thm:fib`. -/
theorem golden_factors (e f : ℤ) :
    f ^ 4 - 3 * e ^ 2 * f ^ 2 + e ^ 4 = (f ^ 2 - e * f - e ^ 2) * (f ^ 2 + e * f - e ^ 2) := by
  ring

/-- **`N₀ = b + 2c`.** -/
theorem N0_eq_b_add_two_c (e f : ℤ) : 3 * f ^ 2 - e ^ 2 = (f ^ 2 - e ^ 2) + 2 * f ^ 2 := by ring

/-- **`f a = e c`** — the trade making `a^f` and `c^e` interchangeable. -/
theorem fa_eq_ec (e f : ℤ) : f * (e * f) = e * f ^ 2 := by ring

/-- The three `j = 0` words, as zero, one and two trades, each spanning `e N₀`. -/
theorem three_trades (e f : ℤ) :
    (0 * (e * f) + e * (f ^ 2 - e ^ 2) + (2 * e) * f ^ 2 = e * (3 * f ^ 2 - e ^ 2))
      ∧ (f * (e * f) + e * (f ^ 2 - e ^ 2) + e * f ^ 2 = e * (3 * f ^ 2 - e ^ 2))
      ∧ ((2 * f) * (e * f) + e * (f ^ 2 - e ^ 2) + 0 * f ^ 2 = e * (3 * f ^ 2 - e ^ 2)) := by
  refine ⟨by ring, by ring, by ring⟩

/-- **`c` splits only at `e = 1`.**  `x a + y b = c` forces `f ∣ y`; `y ≥ f` is impossible on size;
so `y = 0` and `e ∣ f`, hence `e = 1`. -/
theorem c_splits_only_at_e_one (e f x y : ℤ) (he : 1 ≤ e) (hef : e < f) (hcop : IsCoprime e f)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x * (e * f) + y * (f ^ 2 - e ^ 2) = f ^ 2) : e = 1 := by
  have hf : 0 < f := lt_trans (by omega) hef
  have hb : 0 < f ^ 2 - e ^ 2 := by nlinarith
  -- f ∣ y e², hence f ∣ y
  have hdvd : f ∣ y * e ^ 2 := ⟨y * f - f + x * e, by nlinarith [h]⟩
  have hfy : f ∣ y := (hcop.symm.pow_right (n := 2)).dvd_of_dvd_mul_right hdvd
  -- y ≥ f is impossible: it forces f·b ≤ f², i.e. b ≤ f, against e ≤ f-1
  have hy0 : y = 0 := by
    rcases hfy with ⟨k, rfl⟩
    rcases lt_trichotomy k 0 with hk | hk | hk
    · nlinarith
    · simp [hk]
    · exfalso
      have hk1 : 1 ≤ k := hk
      have hf2 : 2 ≤ f := by omega
      have hle : e ≤ f - 1 := by omega
      have hkm : (0:ℤ) ≤ k - 1 := by omega
      have h1 : f * (f ^ 2 - e ^ 2) ≤ f * k * (f ^ 2 - e ^ 2) := by
        nlinarith [mul_nonneg (mul_nonneg hf.le hkm) hb.le]
      have hxa : 0 ≤ x * (e * f) := by positivity
      have h2 : f * (f ^ 2 - e ^ 2) ≤ f ^ 2 := by linarith
      have h3 : f ^ 2 - e ^ 2 ≤ f := by nlinarith
      have h4 : 2 * f - 1 ≤ f ^ 2 - e ^ 2 := by nlinarith
      omega
  subst hy0
  -- x e f = f², so e ∣ f, so e = 1
  have hef2 : e ∣ f := ⟨x, by nlinarith [h]⟩
  have : IsUnit e := hcop.isUnit_of_dvd' (dvd_refl e) hef2
  rcases Int.isUnit_iff.mp this with h1 | h1 <;> omega

/-- **`b < a` iff the golden quartic is negative** — the regime split, stated on the sides. -/
theorem b_lt_a_iff (e f : ℤ) (he : 1 ≤ e) (hef : e < f) :
    f ^ 2 - e ^ 2 < e * f ↔ f ^ 4 - 3 * e ^ 2 * f ^ 2 + e ^ 4 < 0 := by
  have hf : 0 < f := lt_trans (by omega) hef
  have hb : 0 < f ^ 2 - e ^ 2 := by nlinarith
  have ha : 0 < e * f := mul_pos (by omega) hf
  constructor <;> intro h <;> nlinarith

end Erdos634.TileArithmetic

#print axioms Erdos634.TileArithmetic.golden_is_b_sq_minus_a_sq
#print axioms Erdos634.TileArithmetic.golden_factors
#print axioms Erdos634.TileArithmetic.N0_eq_b_add_two_c
#print axioms Erdos634.TileArithmetic.fa_eq_ec
#print axioms Erdos634.TileArithmetic.three_trades
#print axioms Erdos634.TileArithmetic.c_splits_only_at_e_one
#print axioms Erdos634.TileArithmetic.b_lt_a_iff
