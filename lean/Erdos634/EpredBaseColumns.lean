import Erdos634.N1GapSubGolden

/-!
# The base walk equation at `e = f − 1`: a complete solution list, and no dichotomy

Erdős #634.  Written 2026-09-10 against the target named at the foot of
`private/GOAL_PRIMES.md`: *extend the base trichotomy/dichotomy below `f = 2e`.*

## The question

`cor:basedi2e` (VERIFIED) says: if `gcd(e,f) = 1` and `f > 2e`, the base equation

  `x·(ef) + y·(f² − e²) + z·f² = e(3f² − e²)`,   `x, y, z ≥ 0`

has **exactly three** solutions, `(0,e,2e)`, `(f,e,e)`, `(2f,e,0)`, and the `γ`-trap deletes the
third.  `rem:f2esharp` says `f > 2e` is sharp.  Every **sub-golden** member
(`N1GapSubGolden`, `f² < ef + e²`, which is where `N = 83` and the whole family `e = f − 1` live)
violates `f > 2e`, so at those members the base is **not** known to have only two columns — and
that is upstream of, and therefore blocks, the two-configuration crossing list of
`N1GapSubGolden.card_adm_subGolden`.

## The answer, on the family `e = f − 1`

There is **no dichotomy, and no bounded trichotomy either**.  This file computes the solution set
in closed form for the whole family, `f ≥ 3`, and it has `f + 2` elements:

* `epred_base_solutions` — a solution triple is **exactly one of**
  `(0, f−1, 2f−2)`, `(2f, f−1, 0)`, or `(f−k, (k+1)f−1, f−1−k)` for some `0 ≤ k ≤ f−1`.
  (The middle standard column `(f, f−1, f−1)` is the `k = 0` member of the last family.)
* `epred_solution_is_solution` — the converse: every listed triple really solves the equation, with
  all entries `≥ 0`.  So the list is *exact*, not merely an upper bound; the count is `f + 2` and it
  is **unbounded in `f`**.
* `epred_after_gamma_trap` — the `γ`-trap (`z ≥ 1`) and the corner-parallelogram filter
  (`x + z ≥ 4`, `cornerpara_filter`) leave the `k`-family range `0 ≤ k ≤ f − 3`, i.e. **`f − 3`
  extra columns survive both unconditional filters**, together with `(0,f−1,2f−2)` and `k = 0`.
  At `f = 6` (`N = 83`) that is `3`, so the base carries `5` surviving columns, not `2`.

## Why this is a negative, stated sharply

`rem:closepairs` already records that no bound on `k` follows from size, and
`rem:sharpcolumnscope` that "no arithmetic condition can remove" the surviving columns — but both
are per-member computations ("not proved uniformly in `(e,f)`", `rem:closepairbase`).  What is new
here is a **uniform closed form on an infinite family**, which upgrades "we could not bound it" to
"it is provably unbounded": the number of base columns at `e = f − 1` is exactly `f + 2`, and
`N = 2f² + 2f − 1` (`N1GapSubGolden.epred_N`), so it grows like `√(N/2)`.

Consequence for the /goal: **the route "extend `cor:basedi2e` to `f ≤ 2e`" is closed.**  Not
because the technique is wrong, but because the conclusion is false — the `mod f` reduction of
`cor:basedi2e` is not the obstruction, and no other modulus can help, since the extra solutions
genuinely exist.  Any exclusion of these columns must be geometric, exactly as `rem:closepairs`
says.  On the family `e = f − 1` it must exclude an unbounded, explicitly listed set.

## Relation to the existing corpus (Rule 0.5)

`Frontier.base_column_y_form` (`f ∣ y − e`), `Frontier.close_pair_column`,
`Frontier.one_column_per_k`, `prop:sharpcolumn` (`column_criterion`) are the general machinery, and
this file's `k`-parametrisation agrees with them.  `prop:sharpcolumn`(iii) bounds the admissible
`k` by `1 + ⌊(2e−1−f)/(f−e)⌋`, which at `e = f − 1` reads `f − 2` — an *upper* bound.  The content
below is the matching *lower* bound: every `k` in the range really occurs.  Verified against brute
enumeration of the base equation on all coprime `(e,f)` with `e ≤ 60`, `f < 4e + 4`.
-/

namespace Erdos634.EpredBaseColumns

/-- The base walk equation at `e = f − 1`, in `ℤ`.  The tile is `a = ef = f² − f`,
`b = f² − e² = 2f − 1`, `c = f²`, and the base length is `e(3f² − e²) = (f−1)(2f² + 2f − 1)`. -/
def BaseEq (f x y z : ℤ) : Prop :=
  x * (f ^ 2 - f) + y * (2 * f - 1) + z * f ^ 2 = (f - 1) * (2 * f ^ 2 + 2 * f - 1)

/-- Sanity: the coefficients really are the tile `(ef, f²−e², f²)` at `e = f − 1`, and the
right-hand side really is `e(3f² − e²)`. -/
theorem baseEq_unfold (f x y z : ℤ) :
    BaseEq f x y z ↔
      x * ((f - 1) * f) + y * (f ^ 2 - (f - 1) ^ 2) + z * f ^ 2
        = (f - 1) * (3 * f ^ 2 - (f - 1) ^ 2) := by
  unfold BaseEq
  constructor <;> intro h <;> nlinarith [h]

/-! ## Step 1 — the residue of `y` -/

/-- `f ∣ y + 1`, i.e. `y ≡ e (mod f)` with `e = f − 1`.  This is `Frontier.base_column_y_form`
specialised; reproved here in the file's own coordinates. -/
theorem y_residue {f x y z : ℤ} (h : BaseEq f x y z) : f ∣ y + 1 := by
  refine ⟨2 * y - 2 * f ^ 2 + 3 - x + x * f + z * f, ?_⟩
  unfold BaseEq at h
  nlinarith [h]

/-! ## Step 2 — the reduced equation -/

/-- Writing `y = (k+1)f − 1` and dividing by `f`, the base equation becomes
`f(x + z) + (k+1)(2f − 1) − x = 2f² − 1`. -/
theorem reduced {f x z k : ℤ} (hf : 0 < f) (h : BaseEq f x ((k + 1) * f - 1) z) :
    f * (x + z) + (k + 1) * (2 * f - 1) - x = 2 * f ^ 2 - 1 := by
  unfold BaseEq at h
  have hf' : f ≠ 0 := ne_of_gt hf
  refine mul_left_cancel₀ hf' ?_
  nlinarith [h]

/-! ## Step 3 — the complete solution list -/

/-- **The base walk equation at `e = f − 1`, solved completely.**

For `f ≥ 3`, a triple `(x,y,z)` of nonnegative integers solves the base equation iff it is
`(0, f−1, 2f−2)`, or `(2f, f−1, 0)`, or `(f−k, (k+1)f−1, f−1−k)` for some `0 ≤ k ≤ f−1`.

The three columns of `cor:basedi2e` are the first two together with `k = 0`; every `k ≥ 1` is an
*extra* column with `y > e`, and there are `f − 1` of them.  So the trichotomy fails on this whole
family, and the failure is unbounded in `f`. -/
theorem epred_base_solutions {f x y z : ℤ} (hf : 3 ≤ f)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : BaseEq f x y z) :
    (x = 0 ∧ y = f - 1 ∧ z = 2 * f - 2) ∨
    (x = 2 * f ∧ y = f - 1 ∧ z = 0) ∨
    (∃ k : ℤ, 0 ≤ k ∧ k ≤ f - 1 ∧ x = f - k ∧ y = (k + 1) * f - 1 ∧ z = f - 1 - k) := by
  have hf0 : (0:ℤ) < f := by omega
  obtain ⟨t, ht⟩ := y_residue h
  have hk0 : 0 ≤ t - 1 := by nlinarith [hy, ht, hf0]
  have hy' : y = ((t - 1) + 1) * f - 1 := by linarith [ht]
  subst hy'
  set k : ℤ := t - 1 with hkdef
  have hred := reduced hf0 h
  have hdvd : f ∣ x + k := ⟨x + z + 2 * k + 2 - 2 * f, by nlinarith [hred]⟩
  have hkub : k ≤ f - 1 := by nlinarith [hred, hx, hz, hf0]
  have hxub : x ≤ 2 * f := by nlinarith [hred, hz, hk0, hf0]
  by_cases hexc : x + k = 2 * f
  · have hk : k = 0 := by nlinarith [hred, hz, hk0, hx, hf0]
    have hxv : x = 2 * f := by omega
    have hzv : z = 0 := by
      rw [hk, hxv] at hred; nlinarith [hred, hf0]
    exact Or.inr (Or.inl ⟨hxv, by rw [hk]; ring, hzv⟩)
  · have hlt : x + k < 2 * f := by
      rcases lt_trichotomy (x + k) (2 * f) with hl | he | hg
      · exact hl
      · exact absurd he hexc
      · exfalso; nlinarith [hred, hz, hk0, hx, hf0, hg]
    obtain ⟨s, hs⟩ := hdvd
    have hs0 : 0 ≤ s := by nlinarith [hx, hk0, hs, hf0]
    have hs2 : s < 2 := by nlinarith [hs, hlt, hf0]
    interval_cases s
    · have hx0 : x = 0 := by omega
      have hk0' : k = 0 := by omega
      have hzv : z = 2 * f - 2 := by
        rw [hx0, hk0'] at hred; nlinarith [hred, hf0]
      exact Or.inl ⟨hx0, by rw [hk0']; ring, hzv⟩
    · have hxv : x = f - k := by omega
      have hzv : z = f - 1 - k := by
        rw [hxv] at hred; nlinarith [hred, hf0]
      exact Or.inr (Or.inr ⟨k, hk0, hkub, hxv, rfl, hzv⟩)

/-- The converse: every triple in the list really is a nonnegative solution.  Hence the list is
exact and the solution count is `f + 2`. -/
theorem epred_solution_is_solution {f k : ℤ} (hf : 3 ≤ f) (hk0 : 0 ≤ k) (hk : k ≤ f - 1) :
    BaseEq f (f - k) ((k + 1) * f - 1) (f - 1 - k) ∧ 0 ≤ f - k ∧ 0 ≤ f - 1 - k := by
  refine ⟨?_, by omega, by omega⟩
  unfold BaseEq; ring

theorem epred_first_is_solution (f : ℤ) : BaseEq f 0 (f - 1) (2 * f - 2) := by
  unfold BaseEq; ring

theorem epred_last_is_solution (f : ℤ) : BaseEq f (2 * f) (f - 1) 0 := by
  unfold BaseEq; ring

/-- The `k`-family is injective in `k`, so the `f` values `k = 0, …, f−1` give `f` distinct
columns; with the two extremal ones the total is `f + 2`. -/
theorem epred_k_injective {f k k' : ℤ} (hf : 3 ≤ f)
    (h : (k + 1) * f - 1 = (k' + 1) * f - 1) : k = k' := by
  have hf0 : (0:ℤ) < f := by omega
  refine mul_right_cancel₀ (ne_of_gt hf0) ?_
  linarith [h]

/-! ## Step 4 — what the two unconditional filters leave -/

/-- **After the `γ`-trap and the corner parallelogram, `f − 3` extra columns survive.**

The `γ`-trap (`prop:gammatrap`, general in `(e,f)`) forces `z ≥ 1`; the corner parallelogram
(`cornerpara_filter`) forces `x + z ≥ 4` in a word of at least four edges.  On the `k`-family
`(f−k, (k+1)f−1, f−1−k)` these read `k ≤ f − 2` and `k ≤ f − 3`, so the survivors are exactly
`0 ≤ k ≤ f − 3`: the middle standard column `k = 0` plus `f − 3` extra columns.  Together with
`(0, f−1, 2f−2)` — which passes both filters — the base carries `f − 2` surviving columns, against
the **two** that `cor:basedi2e` delivers when `f > 2e`. -/
theorem epred_after_gamma_trap {f k : ℤ} (hf : 3 ≤ f) (hk0 : 0 ≤ k) (hk : k ≤ f - 1) :
    (1 ≤ f - 1 - k ∧ 4 ≤ (f - k) + (f - 1 - k)) ↔ k ≤ f - 3 := by
  constructor
  · rintro ⟨_, h2⟩; omega
  · intro h; exact ⟨by omega, by omega⟩

/-! ## Non-vacuity: `N = 83`, the one open base-β row below `N = 110` -/

/-- At `(e,f) = (5,6)` — tile `(30, 11, 36)`, `N = 83`, base length `415` — the base equation has
**eight** solutions, not three: `f + 2 = 8`. -/
theorem witness_83_solutions :
    BaseEq 6 0 5 10 ∧ BaseEq 6 12 5 0 ∧ BaseEq 6 6 5 5 ∧ BaseEq 6 5 11 4 ∧
    BaseEq 6 4 17 3 ∧ BaseEq 6 3 23 2 ∧ BaseEq 6 2 29 1 ∧ BaseEq 6 1 35 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> · unfold BaseEq; norm_num

/-- And they are the *only* eight: any nonnegative solution at `f = 6` is one of them. -/
theorem witness_83_complete {x y z : ℤ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h : BaseEq 6 x y z) :
    (x = 0 ∧ y = 5 ∧ z = 10) ∨ (x = 12 ∧ y = 5 ∧ z = 0) ∨
    (x = 6 ∧ y = 5 ∧ z = 5) ∨ (x = 5 ∧ y = 11 ∧ z = 4) ∨
    (x = 4 ∧ y = 17 ∧ z = 3) ∨ (x = 3 ∧ y = 23 ∧ z = 2) ∨
    (x = 2 ∧ y = 29 ∧ z = 1) ∨ (x = 1 ∧ y = 35 ∧ z = 0) := by
  rcases epred_base_solutions (by norm_num : (3:ℤ) ≤ 6) hx hy hz h with
    ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨k, hk0, hk, h1, h2, h3⟩
  · exact Or.inl ⟨h1, by omega, by omega⟩
  · exact Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)
  · have hkc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
    rcases hkc with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨by omega, by omega, by omega⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨by omega, by omega, by omega⟩))))))

/-- The three columns of `cor:basedi2e` are *not* all of them at `N = 83`: `(5,11,4)` is a genuine
extra column, with `y = 11 > 5 = e`, and it survives both unconditional filters (`z = 4 ≥ 1`,
`x + z = 9 ≥ 4`).  This is the witness that the target "extend `cor:basedi2e` below `f = 2e`" is
**not** merely unproved but false. -/
theorem witness_83_extra_column_survives :
    BaseEq 6 5 11 4 ∧ (5:ℤ) < 11 ∧ (1:ℤ) ≤ 4 ∧ (4:ℤ) ≤ 5 + 4 := by
  refine ⟨by unfold BaseEq; norm_num, by norm_num, by norm_num, by norm_num⟩

end Erdos634.EpredBaseColumns
