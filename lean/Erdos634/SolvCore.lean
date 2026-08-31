import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.Star
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.LinearCombination

/-!
# The algebraic core of `prop:solv`

Erdős #634, main paper `prop:solv`.  For a primitive `120°` triple with `b = de²`, the condition
`e ∣ (a + b - c)` is equivalent to a parametrisation by an integer `j` with `d < j < 2d`.  The
algebra behind it is here:

* substituting `c = a + et` into `c² = a² + ab + b²` and dividing by `e` gives
  `a(2t - de) = e(de - t)(de + t)`;
* with `2t = ej` that becomes `4a(j - d) = e²(2d - j)(2d + j)`;
* the right side is positive for `0 < j < 2d`, so `j > d`.

At `d = 1` the interval `(1, 2)` holds no integer, which is `lem:nonint` again — recorded here as a
corollary so the two proofs are visibly the same one.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.SolvCore

/-- **The substituted equation.**  `c = a + et` in `c² = a² + ab + b²` with `b = de²`. -/
theorem core_identity (d e a t : ℤ) (he : e ≠ 0)
    (heq : (a + e * t) ^ 2 = a ^ 2 + a * (d * e ^ 2) + (d * e ^ 2) ^ 2) :
    a * (2 * t - d * e) = e * (d * e - t) * (d * e + t) := by
  have h : e * (a * (2 * t - d * e) - e * (d * e - t) * (d * e + t)) = 0 := by
    linear_combination heq
  rcases mul_eq_zero.mp h with h0 | h0
  · exact absurd h0 he
  · linarith

/-- **The `j`-form.**  With `2t = ej`. -/
theorem j_identity (d e a t j : ℤ) (he : e ≠ 0) (h2t : 2 * t = e * j)
    (h : a * (2 * t - d * e) = e * (d * e - t) * (d * e + t)) :
    4 * a * (j - d) = e ^ 2 * (2 * d - j) * (2 * d + j) := by
  have h4 : e * (4 * a * (j - d) - e ^ 2 * (2 * d - j) * (2 * d + j)) = 0 := by
    linear_combination 4 * h - (4 * a + e * (e * j + 2 * t)) * h2t
  rcases mul_eq_zero.mp h4 with h0 | h0
  · exact absurd h0 he
  · linarith

/-- **`j` exceeds `d`.**  For `0 < j < 2d` and `a > 0` the right side is positive, so `j > d`. -/
theorem j_gt_d (d e a j : ℤ) (ha : 0 < a) (he : e ≠ 0) (hj0 : 0 < j) (hj2 : j < 2 * d)
    (h : 4 * a * (j - d) = e ^ 2 * (2 * d - j) * (2 * d + j)) : d < j := by
  have he2 : 0 < e ^ 2 := by positivity
  have hpos : 0 < e ^ 2 * (2 * d - j) * (2 * d + j) := by
    apply mul_pos (mul_pos he2 (by linarith)) (by linarith)
  nlinarith [h, hpos, ha]

/-- **At `d = 1` there is no such `j`**, which is `lem:nonint` in this language: `1 < j < 2` is
empty. -/
theorem no_j_at_d_one (j : ℤ) (h1 : 1 < j) (h2 : j < 2) : False := by omega

/-! ## The proposition itself

The paper's `prop:solv` characterises `e ∣ (a + b - c)` for a `120°` triple with `b = de²` by the
existence of an integer `j` with `d < j < 2d` and `ej` even, through the displayed formula for `a`
and `c = a + e²j/2`.  Both are written here without division: the formula for `a` is
`4a(j - d) = e²(2d - j)(2d + j)` and the one for `c` is `2c = 2a + e²j`. -/

/-- **`prop:solv`.**  For a positive `120°` triple with `b = de²` and `a` coprime to `e`, the
divisibility `e ∣ (a + b - c)` holds exactly when the parametrisation by `j` does. -/
theorem solv_iff (d e a b c : ℤ) (hd : 1 ≤ d) (he : 1 ≤ e) (hb : b = d * e ^ 2)
    (ha : 0 < a) (hcop : IsCoprime a e) (htriple : c ^ 2 = a ^ 2 + a * b + b ^ 2) (hc : 0 < c) :
    e ∣ (a + b - c) ↔
      ∃ j : ℤ, d < j ∧ j < 2 * d ∧ 2 ∣ e * j ∧
        4 * a * (j - d) = e ^ 2 * (2 * d - j) * (2 * d + j) ∧ 2 * c = 2 * a + e ^ 2 * j := by
  have he0 : (0:ℤ) < e := by linarith
  have hbpos : 0 < b := by rw [hb]; positivity
  constructor
  · intro hdvd
    -- `c ≡ a (mod e)` and `0 < c - a < b`
    have hca : e ∣ (c - a) := by
      have : c - a = b - (a + b - c) := by ring
      rw [this]
      exact dvd_sub (by rw [hb]; exact ⟨d * e, by ring⟩) hdvd
    obtain ⟨t, ht⟩ := hca
    have hcgt : a < c := by nlinarith
    have hclt : c < a + b := by nlinarith
    have ht0 : 0 < t := by nlinarith
    have htd : t < d * e := by
      have : e * t < d * e ^ 2 := by rw [← hb]; linarith [ht]
      nlinarith
    -- the substituted equation
    have hct : c = a + e * t := by linarith [ht]
    have hcore : a * (2 * t - d * e) = e * (d * e - t) * (d * e + t) := by
      refine core_identity d e a t (ne_of_gt he0) ?_
      rw [← hct, ← hb]; exact htriple
    -- `e ∣ 2t`
    have hdvd2 : e ∣ a * (2 * t - d * e) := ⟨(d * e - t) * (d * e + t), by linarith [hcore]⟩
    have hdvd3 : e ∣ (2 * t - d * e) := hcop.symm.dvd_of_dvd_mul_left hdvd2
    have hdvd4 : e ∣ 2 * t := by
      have h : 2 * t = (2 * t - d * e) + e * d := by ring
      rw [h]; exact dvd_add hdvd3 ⟨d, rfl⟩
    obtain ⟨j, hj⟩ := hdvd4
    have hj0 : 0 < j := by nlinarith
    have hj2 : j < 2 * d := by nlinarith
    have hjid : 4 * a * (j - d) = e ^ 2 * (2 * d - j) * (2 * d + j) :=
      j_identity d e a t j (ne_of_gt he0) hj hcore
    exact ⟨j, j_gt_d d e a j ha (ne_of_gt he0) hj0 hj2 hjid, hj2, ⟨t, by linarith [hj]⟩, hjid,
      by rw [hct]; linear_combination e * hj⟩
  · rintro ⟨j, hjd, hj2, ⟨k, hk⟩, hform, hcj⟩
    have h2 : 2 * (a + b - c) = 2 * (e * (d * e - k)) := by
      rw [hb]; linear_combination -hcj - e * hk
    exact ⟨d * e - k, mul_left_cancel₀ (two_ne_zero) h2⟩

end Erdos634.SolvCore
