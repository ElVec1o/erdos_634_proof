import Mathlib.Tactic

/-!
# The layer word is `a^f` or `c^e`, and nothing else

Erdős #634 — pinning the block vocabulary of the deep rogue's column.

`StripRigid` shows the strip is uniquely tiled and presents `a^f` upward across `[0, ec]`.
`StripRigid.no_tower_fills` kills every tower assembled from `a`-strips (height `c`) and
`c`-bands (height `a`).  The gap between them was the vocabulary: nothing said those were the
only two blocks.  This file closes that gap.

## The statement

A layer interface spans `ec`, so the tile edges presented across it solve

  `x a + y b + z c = e c`,  `x, y, z ≥ 0`,

for the tile `(a,b,c) = (ef, f² - e², f²)`.  The only solutions are `(f,0,0)` and `(0,e·0,e)`,
that is **`a^f` or `c^e`** — `word_classification`.  No `b` edge ever appears, and no mixed word
of `a`s and `c`s is possible.

## The proof

Four steps, all elementary, and the third is the whole content.

1. Reduce mod `f`: the equation gives `f ∣ y e²`, and `gcd(e,f) = 1` gives `f ∣ y`.  Write
   `y = f y'` and divide through by `f`:  `x e + y'(f² - e²) + z f = e f`.
2. Reduce mod `e`: that gives `e ∣ f (y' f + z)`, hence `e ∣ y' f + z`.  Write `y' f + z = e w`.
3. Substituting collapses the equation to `x = f(1 - w) + y' e`.  Now suppose `y' ≥ 1`.  From
   `z ≥ 0` we get `e w ≥ y' f > y' e`, so `w > y'`.  From `x ≥ 0` we get
   `f w ≤ f + y' e < f + y' f`, so `w < y' + 1`.  Hence `y' < w < y' + 1` with `w` an integer:
   impossible.  So `y' = 0`, and `y = 0`.
4. With `y' = 0`: `z = e w` and `x = f(1 - w)`, so nonnegativity pins `w ∈ {0, 1}`, giving
   `(f,0,0)` and `(0,0,e)`.

Step 3 is where `e < f` does all the work, twice and in opposite directions: `f > e` opens the
interval below `w`, `e < f` closes it above, and the integer `w` is squeezed into the open unit
interval `(y', y' + 1)`.

Falsified first, per protocol: brute-force solution sets computed for every coprime member with
`f < 45` (603 members) and again for `e ≥ 2`, `f < 60` (1027 members).  Extra solutions: 0.

## What this buys, and what it does not

Combined with `StripRigid`, every `a`-layer is rigid: reflection is excluded at every position, so
an `a^f` interface forces a strip of height exactly `c` and hands `a^f` up again.  A `c^e`
interface likewise carries apices at height `a`.  With the vocabulary pinned to these two blocks,
`no_tower_fills` applies and the deep rogue dies.

Two hypotheses in that chain are **not** yet proved and are stated as such:

* that the interface has a breakpoint at `s = ec` from above, so the layer word is a finite word
  of total length exactly `ec` (the column's right boundary is not known to be a wall);
* that a `c`-layer closes flush at height `a`.  Unlike `a`-layers, `c`-layers are **not** rigid:
  the reflected placement has apex offset `D = 2a cos β = e² N₀ / f²`, and `D/c = u(3-u)` with
  `u = e²/f²`, so the reflected tile clears the mast exactly when `e/f < 1/φ`.  The overlap
  argument that kills reflection in `a`-layers does not fire here, since `D < 2c` always.

The golden ratio reappearing at that split is the same `b² + ab - a²` that governs the second-edge
quartic, and is recorded for that reason.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.LayerWord

/-- **The layer word classification.**  Across an interface of length `e c`, the only edge
multisets a tiling can present are `a^f` and `c^e`.  In particular no `b` edge occurs, and the
two blocks of `no_tower_fills` are the only blocks. -/
theorem word_classification (e f x y z : ℤ) (he : 1 ≤ e) (hef : e < f)
    (hcop : IsCoprime e f) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (heq : x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 = e * f ^ 2) :
    (x = f ∧ y = 0 ∧ z = 0) ∨ (x = 0 ∧ y = 0 ∧ z = e) := by
  have hf : 0 < f := lt_trans (by omega) hef
  have he0 : (e : ℤ) ≠ 0 := by omega
  have hf0 : (f : ℤ) ≠ 0 := by omega
  -- step 1: f ∣ y
  have h1 : f ∣ y := by
    have hdvd : f ∣ y * e ^ 2 := ⟨y * f - e * f + x * e + z * f, by linarith [heq]; ⟩
    exact (hcop.symm.pow_right (n := 2)).dvd_of_dvd_mul_right hdvd
  obtain ⟨y', rfl⟩ := h1
  -- divide the equation by f
  have h2 : x * e + y' * (f ^ 2 - e ^ 2) + z * f = e * f := by
    have : f * (x * e + y' * (f ^ 2 - e ^ 2) + z * f) = f * (e * f) := by ring_nf; ring_nf at heq; linarith
    exact mul_left_cancel₀ hf0 this
  -- step 2: e ∣ y' f + z
  have h3 : e ∣ y' * f + z := by
    have hdvd : e ∣ f * (y' * f + z) := ⟨f - x + y' * e, by linarith [h2]⟩
    exact hcop.dvd_of_dvd_mul_left hdvd
  obtain ⟨w, hw⟩ := h3
  -- step 3: substituting collapses to x = f(1-w) + y' e
  have h4 : x = f * (1 - w) + y' * e := by
    have : e * x = e * (f * (1 - w) + y' * e) := by nlinarith [h2, hw]
    exact mul_left_cancel₀ he0 this
  have hy'0 : 0 ≤ y' := by nlinarith
  -- the squeeze: y' ≥ 1 forces the integer w into the open interval (y', y'+1)
  have hy' : y' = 0 := by
    by_contra hne
    have hy'1 : 1 ≤ y' := by omega
    have hzw : y' * f ≤ e * w := by nlinarith [hw]
    have hlo : y' < w := by nlinarith
    have hhi : w < y' + 1 := by nlinarith
    omega
  subst hy'
  -- step 4: w ∈ {0,1}
  simp only [zero_mul, zero_add] at hw h4
  have hw0 : 0 ≤ w := by nlinarith
  have hw1 : w ≤ 1 := by nlinarith
  interval_cases w
  · left; refine ⟨by linarith [h4], by ring, by nlinarith [hw]⟩
  · right; refine ⟨by linarith [h4], by ring, by nlinarith [hw]⟩

/-- No `b` edge ever appears across a layer interface. -/
theorem no_b_edge (e f x y z : ℤ) (he : 1 ≤ e) (hef : e < f) (hcop : IsCoprime e f)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (heq : x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 = e * f ^ 2) : y = 0 := by
  rcases word_classification e f x y z he hef hcop hx hy hz heq with ⟨_, h, _⟩ | ⟨_, h, _⟩ <;> exact h

/-- The two blocks are exclusive: a layer is `a^f` or `c^e`, never a mixture. -/
theorem no_mixed_word (e f x y z : ℤ) (he : 1 ≤ e) (hef : e < f) (hcop : IsCoprime e f)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (heq : x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 = e * f ^ 2) :
    x = 0 ∨ z = 0 := by
  rcases word_classification e f x y z he hef hcop hx hy hz heq with ⟨_, _, h⟩ | ⟨h, _, _⟩
  · exact Or.inr h
  · exact Or.inl h

/-- Both blocks are realized, so the classification is sharp: `a^f` spans `ec`. -/
theorem a_block_spans (e f : ℤ) : f * (e * f) + 0 * (f ^ 2 - e ^ 2) + 0 * f ^ 2 = e * f ^ 2 := by
  ring

/-- and `c^e` spans `ec`. -/
theorem c_block_spans (e f : ℤ) : 0 * (e * f) + 0 * (f ^ 2 - e ^ 2) + e * f ^ 2 = e * f ^ 2 := by
  ring

/-- **The `c`-layer reflection offset.**  `D = 2 a cos β = (a² + c² - b²)/c = e² N₀ / f²`, cleared:
`f² D = e² N₀`.  Unlike the `a`-layer's `S`, this satisfies `D < 2c` always, so the overlap
argument of `StripRigid` does not fire and `c`-layers are not rigid. -/
theorem c_layer_offset (e f : ℤ) :
    (e * f) ^ 2 + (f ^ 2) ^ 2 - (f ^ 2 - e ^ 2) ^ 2 = e ^ 2 * (3 * f ^ 2 - e ^ 2) := by ring

/-- `D < 2c` for every member, cleared by `f²`: `e² N₀ < 2 f⁴`.  This is why the `a`-layer
overlap argument has no `c`-layer analogue. -/
theorem c_offset_lt_two_c (e f : ℤ) (he : 1 ≤ e) (hef : e < f) :
    e ^ 2 * (3 * f ^ 2 - e ^ 2) < 2 * f ^ 4 := by
  have hf : 0 < f := lt_trans (by omega) hef
  have hv : e ^ 2 < f ^ 2 := by nlinarith
  -- 2f⁴ - e²(3f² - e²) = (2f² - e²)(f² - e²) > 0
  nlinarith [mul_pos (show (0:ℤ) < 2 * f ^ 2 - e ^ 2 by nlinarith)
                     (show (0:ℤ) < f ^ 2 - e ^ 2 by nlinarith)]

end Erdos634.LayerWord

#print axioms Erdos634.LayerWord.word_classification
#print axioms Erdos634.LayerWord.no_b_edge
#print axioms Erdos634.LayerWord.no_mixed_word
#print axioms Erdos634.LayerWord.a_block_spans
#print axioms Erdos634.LayerWord.c_block_spans
#print axioms Erdos634.LayerWord.c_layer_offset
#print axioms Erdos634.LayerWord.c_offset_lt_two_c
