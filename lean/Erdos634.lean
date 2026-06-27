import Mathlib.Tactic
import Mathlib.RingTheory.Coprime.Basic

/-!
# Erdős Problem #634 — the arithmetic core of the Φ-invariant proof

For a primitive 120°-triple `(a, b, c)` (`gcd = 1`, `c² = a² + ab + b²`) whose squared leg is
`b = k²`, the integer `k` does **not** divide `a + b − c`.  Equivalently the Φ-invariant
tile-count `M = (c − a − b)/k` is never an integer, so no prime number of 2π/3 tiles tiles an
isosceles triangle; with the classification of the other Laczkovich branches this resolves the
conjecture that no prime `≡ 3 (mod 4)` is achievable (Erdős #634).

Only `gcd(a, k) = 1` is used (for a primitive triple `gcd(a,b)=1`, so `gcd(a,k)=gcd(a,k²)=1`).

## Scope of this formalization

What is **machine-checked here** is the *novel arithmetic heart* of the proof — the statement that
`M = (c−a−b)/k` is never an integer (`k_not_dvd_sum_sub`, and the corollary `M_not_int`). The
*geometric* ingredients of the paper (the Φ-invariant's cancellation and tile-value lemmas, the
shape classification, Laczkovich's case analysis, and Beeson's equilateral input) are **not**
formalized: there is at present no theory of triangle dissections in Mathlib, so those parts remain
in the human-checked paper. This file pins the one genuinely new number-theoretic claim to a
machine-checked, axiom-clean proof.
-/

namespace Erdos634

/-- **Arithmetic core.** `a, k > 0`, `IsCoprime a k`, `c > 0`, `c² = a² + a·k² + k⁴`
(i.e. `c² = a² + ab + b²` with `b = k²`).  Then `k ∤ (a + k² − c)`. -/
theorem k_not_dvd_sum_sub
    (a k c : ℤ) (ha : 0 < a) (hk : 0 < k) (hcop : IsCoprime a k)
    (hc2 : c ^ 2 = a ^ 2 + a * k ^ 2 + k ^ 4) (hc : 0 < c) :
    ¬ (k ∣ (a + k ^ 2 - c)) := by
  have hk2 : 0 < k ^ 2 := by positivity
  -- c > a
  have hca : a < c := by nlinarith [mul_pos ha hk2, sq_nonneg (c - a), sq_nonneg (c + a)]
  -- c < a + k²
  have hcab : c < a + k ^ 2 := by
    nlinarith [mul_pos ha hk2, sq_nonneg (a + k ^ 2 - c), sq_nonneg (a + k ^ 2 + c)]
  rintro hdvd
  -- k ∣ (c − a)
  have hkk2 : k ∣ k ^ 2 := dvd_pow_self k (by norm_num)
  have hdca : k ∣ (c - a) := by
    have h1 : k ∣ (a + k ^ 2 - c - k ^ 2) := dvd_sub hdvd hkk2
    have h2 : a + k ^ 2 - c - k ^ 2 = -(c - a) := by ring
    rw [h2] at h1
    exact (dvd_neg).mp h1
  obtain ⟨t, ht⟩ := hdca           -- c - a = k * t
  -- 1 ≤ t and t < k
  have htpos : 0 < t := by
    have h : 0 < k * t := by rw [← ht]; linarith
    exact (mul_pos_iff_of_pos_left hk).mp h
  have htlt : t < k := by
    have h : k * t < k * k := by rw [← ht]; nlinarith
    exact lt_of_mul_lt_mul_left h (le_of_lt hk)
  -- c = a + k t
  have hc' : c = a + k * t := by linarith [ht]
  -- key factorization:  a (2t − k) = k (k − t)(k + t)
  have hrel : a * (2 * t - k) = k * ((k - t) * (k + t)) := by
    have : c ^ 2 = (a + k * t) ^ 2 := by rw [hc']
    nlinarith [this, hc2]
  -- k ∣ a (2t − k), and IsCoprime a k ⇒ k ∣ (2t − k) ⇒ k ∣ 2t
  have hdvd2 : k ∣ a * (2 * t - k) := ⟨(k - t) * (k + t), hrel⟩
  have hk2t : k ∣ (2 * t - k) := (hcop.symm).dvd_of_dvd_mul_left hdvd2
  have hk2t' : k ∣ 2 * t := by
    have := dvd_add hk2t (dvd_refl k)
    simpa using this
  -- 0 < 2t < 2k and k ∣ 2t ⇒ 2t = k
  obtain ⟨m, hm⟩ := hk2t'
  have hmpos : 0 < m := by
    have : 0 < k * m := by rw [← hm]; linarith
    exact (mul_pos_iff_of_pos_left hk).mp this
  have hmlt : m < 2 := by
    have h : k * m < k * 2 := by rw [← hm]; nlinarith
    exact lt_of_mul_lt_mul_left h (le_of_lt hk)
  have hm1 : m = 1 := by omega
  have h2t : 2 * t = k := by rw [hm, hm1, mul_one]
  -- contradiction: LHS = 0 but RHS > 0
  have hlhs : a * (2 * t - k) = 0 := by rw [h2t]; ring
  have hrhs : 0 < k * ((k - t) * (k + t)) := by
    have h1 : 0 < k - t := by linarith
    have h2 : 0 < k + t := by linarith
    positivity
  rw [hlhs] at hrel
  linarith [hrel ▸ hrhs]

/-- **The Φ-invariant tile count is never an integer.** Under the same hypotheses, there is no
integer `M` with `c − a − k² = M·k`; i.e. `M = (c − a − b)/k ∉ ℤ`.  This is the contradiction that
forbids a prime number of `2π/3`-tiles from tiling an isosceles triangle. -/
theorem M_not_int
    (a k c : ℤ) (ha : 0 < a) (hk : 0 < k) (hcop : IsCoprime a k)
    (hc2 : c ^ 2 = a ^ 2 + a * k ^ 2 + k ^ 4) (hc : 0 < c) :
    ¬ ∃ M : ℤ, c - a - k ^ 2 = M * k := by
  rintro ⟨M, hM⟩
  -- `k ∣ (a + k² − c)` since `a + k² − c = -(c - a - k²) = -(M*k) = (-M)*k`
  exact k_not_dvd_sum_sub a k c ha hk hcop hc2 hc ⟨-M, by linarith [hM]⟩

end Erdos634

-- Axiom audit: only the standard `propext`, `Classical.choice`, `Quot.sound`.
#print axioms Erdos634.k_not_dvd_sum_sub
#print axioms Erdos634.M_not_int
