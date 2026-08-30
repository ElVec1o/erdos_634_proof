import Mathlib

/-!
# Non-integrality

Erdős #634, main paper `lem:nonint`.  A step in the spectrum chain, and pure number theory: for a
`120°` triple with `b` a square coprime to `a`, the side combination `a + b - c` is never divisible
by the square root of `b`.

The paper's proof is followed exactly: `a < c < a + b` pins `c - a` strictly between `0` and `k²`;
divisibility writes `c = a + kt` with `0 < t < k`; substituting and dividing by `k` gives
`a(2t - k) = k(k - t)(k + t)`; coprimality forces `k ∣ 2t`, so `2t = k`, and then the left side
vanishes while the right side does not.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.NonIntegrality

/-- **Non-integrality.**  With `b = k²`, `gcd(a, k) = 1` and `c² = a² + ab + b²`, `k` does not
divide `a + b - c`. -/
theorem k_not_dvd (a k c : ℤ) (ha : 0 < a) (hk : 0 < k) (hc : 0 < c)
    (hcop : IsCoprime a k) (heq : c ^ 2 = a ^ 2 + a * k ^ 2 + (k ^ 2) ^ 2) :
    ¬ (k ∣ (a + k ^ 2 - c)) := by
  intro hdvd
  -- `a < c < a + k²`
  have hca : a < c := by nlinarith
  have hcab : c < a + k ^ 2 := by nlinarith
  -- so `k ∣ c - a` with `0 < c - a < k²`
  have hdvd' : k ∣ (c - a) := by
    have : c - a = k ^ 2 - (a + k ^ 2 - c) := by ring
    rw [this]
    exact dvd_sub (Dvd.intro k (by ring)) hdvd
  obtain ⟨t, ht⟩ := hdvd'
  have ht0 : 0 < t := by nlinarith
  have htk : t < k := by nlinarith
  -- the substituted equation, divided by `k`
  have hkey : a * (2 * t - k) = k * (k - t) * (k + t) := by
    have hc' : c = a + k * t := by linarith [ht]
    have hexp : k * (a * (2 * t - k) - (k - t) * (k + t) * k) = 0 := by
      rw [hc'] at heq; nlinarith [heq]
    have hk0 : k ≠ 0 := ne_of_gt hk
    have := mul_eq_zero.mp hexp
    rcases this with h | h
    · exact absurd h hk0
    · linarith [h]
  -- coprimality forces `k ∣ 2t`, hence `2t = k`
  have hdvd2 : k ∣ a * (2 * t - k) := ⟨(k - t) * (k + t), by linarith [hkey]⟩
  have hdvd3 : k ∣ (2 * t - k) := (hcop.symm.dvd_of_dvd_mul_left hdvd2)
  have hdvd4 : k ∣ 2 * t := by
    have : 2 * t = (2 * t - k) + k := by ring
    rw [this]; exact dvd_add hdvd3 dvd_rfl
  obtain ⟨u, hu⟩ := hdvd4
  have hu1 : u = 1 := by nlinarith
  have h2t : 2 * t = k := by rw [hu, hu1]; ring
  -- then the left side vanishes and the right side does not
  rw [h2t] at hkey
  -- `a·0 = k(k-t)(k+t)`, but every factor on the right is positive
  have hzero : (0:ℤ) = k * (k - t) * (k + t) := by linarith [hkey]
  have hpos : 0 < k * (k - t) * (k + t) := by
    apply mul_pos (mul_pos hk (by linarith)) (by linarith)
  linarith [hzero, hpos]

end Erdos634.NonIntegrality
