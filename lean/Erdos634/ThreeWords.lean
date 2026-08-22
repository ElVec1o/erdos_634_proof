import Mathlib.Tactic

/-!
# Above `f = 2e` there are exactly three base words

Erdős #634 — reducing `hyp:walls` from a hypothesis to two explicit exclusions.

`WallsWord` shows `hyp:walls` pins the base word to `a^f b^e c^e`, so

> `hyp:walls` at `(e,f)` ⟺ no tiling carries any *other* base word.

This file bounds how many "others" there are.  For every member with `f > 2e` the base-word set is
**exactly three**:

  `(n_a, Q, n_c) = (0, e, 2e)`,  `(f, e, e)` — the walls word,  `(2f, e, 0)`.

So above `f = 2e`, `hyp:walls` is precisely the statement that **two** explicit words admit no
tiling — `three_words`.

## The proof

From the family `n_a = j e + f t`, `n_c = 2e - t e - j f`, nonnegativity of both gives, after
multiplying by `f` and `e` and chaining, `j (f² - e²) ≤ 2 e f` — with no `γ`-trap needed, so it
covers `R = 0` as well.

Suppose `j ≥ 1`.  Then `j f ≥ f > 2e`, so `t e ≤ 2e - j f < 0` and `t ≤ -1`.  Feeding `t ≤ -1` back
into `f t ≥ -j e` gives `j e ≥ f > 2e`, hence `j ≥ 3`.  But then
`3(f² - e²) ≤ j(f² - e²) ≤ 2 e f`, which `f > 2e` contradicts.  So `j = 0`, and then `f t ≥ 0` and
`2e - t e ≥ 0` pin `t ∈ {0, 1, 2}`.

Verified against brute-force enumeration of `P a + Q b + R c = e N₀`: all 1227 coprime members with
`f > 2e` and `f < 90` give exactly these three, and all 543 members with `f ≤ 2e` give strictly
more.

## Status of the two extra words

Both are dead at every member the engine has reached.  `(2f, e, 0)` dies especially cheaply —
17, 284, 274, 2604, 1392, 29488 nodes at `(1,2), (2,3), (1,3), (3,4), (1,4), (4,5)` — which suggests
a local obstruction rather than a search accident, and is the natural next target for a proof.

Where all three die, the target has **no tiling at all** and the exclusion is unconditional.  That
already reproduces the known exclusions `N = 11, 23, 26, 47` from a complete three-case analysis,
and settles `N = 39`.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.ThreeWords

/-- The nonnegativity bound, valid with or without a `c`-edge on the base. -/
theorem j_bound (e f j t : ℤ) (he : 1 ≤ e) (hef : e < f)
    (hna : 0 ≤ j * e + f * t) (hnc : 0 ≤ 2 * e - t * e - j * f) :
    j * (f ^ 2 - e ^ 2) ≤ 2 * e * f := by
  have hf : 0 < f := lt_trans (by omega) hef
  have he0 : (0:ℤ) ≤ e := by omega
  have h1 : (t * e + j * f) * f ≤ (2 * e) * f :=
    mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hf)
  have h2 : (0:ℤ) ≤ (j * e + f * t) * e := mul_nonneg hna he0
  nlinarith [h1, h2]

/-- **Exactly three base words above `f = 2e`.**  Nonnegativity forces `j = 0` and `t ∈ {0,1,2}`,
giving `(0,e,2e)`, `(f,e,e)` and `(2f,e,0)`. -/
theorem three_words (e f j t : ℤ) (he : 1 ≤ e) (h2e : 2 * e < f) (hj : 0 ≤ j)
    (hna : 0 ≤ j * e + f * t) (hnc : 0 ≤ 2 * e - t * e - j * f) :
    j = 0 ∧ 0 ≤ t ∧ t ≤ 2 := by
  have hef : e < f := by omega
  have hf : 0 < f := by omega
  have hkey := j_bound e f j t he hef hna hnc
  have hj0 : j = 0 := by
    by_contra hne
    have hj1 : 1 ≤ j := by omega
    -- j f ≥ f > 2e forces t e < 0, so t ≤ -1
    have hjf : f ≤ j * f := le_mul_of_one_le_left (le_of_lt hf) hj1
    have hte : t * e < 0 := by nlinarith
    have ht1 : t ≤ -1 := by nlinarith
    -- t ≤ -1 with f t ≥ -j e gives j e ≥ f
    have hje : f ≤ j * e := by nlinarith
    -- hence j ≥ 3, and the bound collapses
    have hj3 : 3 ≤ j := by nlinarith
    nlinarith [hkey, hj3]
  subst hj0
  exact ⟨rfl, by nlinarith, by nlinarith⟩

/-- The three words, verified to solve the base equation `n_a a + Q b + n_c c = e N₀`. -/
theorem the_three (e f : ℤ) :
    (0 * (e * f) + e * (f ^ 2 - e ^ 2) + (2 * e) * f ^ 2 = e * (3 * f ^ 2 - e ^ 2))
      ∧ (f * (e * f) + e * (f ^ 2 - e ^ 2) + e * f ^ 2 = e * (3 * f ^ 2 - e ^ 2))
      ∧ ((2 * f) * (e * f) + e * (f ^ 2 - e ^ 2) + 0 * f ^ 2 = e * (3 * f ^ 2 - e ^ 2)) := by
  refine ⟨by ring, by ring, by ring⟩

end Erdos634.ThreeWords

#print axioms Erdos634.ThreeWords.j_bound
#print axioms Erdos634.ThreeWords.three_words
#print axioms Erdos634.ThreeWords.the_three
