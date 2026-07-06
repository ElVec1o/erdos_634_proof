import Mathlib.Tactic
import Mathlib.NumberTheory.SumTwoSquares

/-!
# Erdős Problem #634 — the arithmetic core of the Φ-invariant proof

For a primitive 120°-triple `(a, b, c)` (`gcd = 1`, `c² = a² + ab + b²`) whose squared leg is
`b = k²`, the integer `k` does **not** divide `a + b − c`.  Equivalently the Φ-invariant tile-count
`M = (c − a − b)/k` is never an integer, so no prime number of `2π/3` tiles tiles an isosceles
triangle; with the classification of the other Laczkovich branches this resolves the conjecture that
no prime `≡ 3 (mod 4)` is achievable (Erdős #634).

This file machine-checks the **arithmetic layer** of the argument, axiom-clean (only `propext`,
`Classical.choice`, `Quot.sound`):

* `k_not_dvd_sum_sub`, `M_not_int` — the Φ-invariant tile count is never an integer.
* `iso_reduction_identity` — the algebraic identity behind the isosceles boundary reduction.
* `add_not_prime` — for a 120°-triple, `a + b` is never prime (over ℤ; coprimality not even
  needed — it holds for every positive `a, b, c` with `c² = a² + ab + b²`).
* `prime_three_mod_four_excluded` — a prime `≡ 3 (mod 4)` exceeding `3` is none of the
  commensurable-angle forms `{square, sum of two squares, 2·□, 3·□, 6·□}` (Beeson–Laczkovich),
  using Fermat's two-squares theorem from Mathlib (`Nat.eq_sq_add_sq_iff`).

The *geometric* ingredients of the paper (the Φ-invariant's cancellation and tile-value lemmas, the
shape classification, Laczkovich's case analysis, Beeson's equilateral input) are **not** formalized
— there is no theory of triangle dissections in Mathlib — and remain human-checked in the paper.
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

/-- **The Φ-invariant tile count is never an integer.** -/
theorem M_not_int
    (a k c : ℤ) (ha : 0 < a) (hk : 0 < k) (hcop : IsCoprime a k)
    (hc2 : c ^ 2 = a ^ 2 + a * k ^ 2 + k ^ 4) (hc : 0 < c) :
    ¬ ∃ M : ℤ, c - a - k ^ 2 = M * k := by
  rintro ⟨M, hM⟩
  exact k_not_dvd_sum_sub a k c ha hk hcop hc2 hc ⟨-M, by linarith [hM]⟩

/-- **Theorem A (isosceles reduction identity).** -/
theorem iso_reduction_identity
    (a k c : ℤ) (_ha : 0 < a) (_hk : 0 < k)
    (hc2 : c ^ 2 = a ^ 2 + a * k ^ 2 + k ^ 4) :
    (c - a - k ^ 2) * (c + a - k ^ 2) = k ^ 2 * (a + 2 * k ^ 2 - 2 * c) := by
  nlinarith [hc2]

/-- **Theorem B (a+b is never prime for a primitive 120-triple).** -/
theorem add_not_prime
    (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (_hcop : IsCoprime a b)
    (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) (hc : 0 < c) :
    ¬ Prime (a + b) := by
  intro hp
  -- basic bounds
  have hab : 0 < a + b := by linarith
  have hca : a < c := by nlinarith [mul_pos ha hb, sq_nonneg (c - a)]
  have hcb : b < c := by nlinarith [mul_pos ha hb, sq_nonneg (c - b)]
  have hcp : c < a + b := by nlinarith [mul_pos ha hb, sq_nonneg (a + b - c), sq_nonneg (a + b + c)]
  set p := a + b with hpdef
  -- factorization 3 p² = X * Y  with  X = 2c - a + b,  Y = 2c + a - b
  have hXY : 3 * p ^ 2 = (2 * c - a + b) * (2 * c + a - b) := by
    have : (a - b) ^ 2 = 4 * c ^ 2 - 3 * p ^ 2 := by rw [hpdef]; nlinarith [hc2]
    nlinarith [this]
  set X := 2 * c - a + b with hXdef
  set Y := 2 * c + a - b with hYdef
  have hXpos : 0 < X := by rw [hXdef]; nlinarith [hcp, hab]
  have hYpos : 0 < Y := by rw [hYdef]; nlinarith [hcp, hab]
  have hXlt : X < 3 * p := by rw [hXdef, hpdef]; linarith [hcp]
  have hYlt : Y < 3 * p := by rw [hYdef, hpdef]; linarith [hcp]
  -- p divides X*Y
  have hpdvd : p ∣ X * Y := ⟨3 * p, by linarith [hXY]⟩
  -- p prime ⇒ p ∣ X or p ∣ Y
  have hpX_or_hpY : p ∣ X ∨ p ∣ Y := hp.dvd_mul.mp hpdvd
  -- a helper: if p ∣ Z with 0 < Z < 3p then Z = p or Z = 2p
  have step : ∀ Z W : ℤ, 0 < Z → Z < 3 * p → 0 < W → W < 3 * p → Z * W = 3 * p ^ 2 →
      p ∣ Z → 4 * c = Z + W → False := by
    intro Z W hZpos hZlt hWpos hWlt hZW hpZ h4cZW
    obtain ⟨u, hu⟩ := hpZ         -- Z = p * u
    have hppos : 0 < p := hab
    have hupos : 0 < u := by
      have : 0 < p * u := by rw [← hu]; exact hZpos
      exact (mul_pos_iff_of_pos_left hppos).mp this
    have hult : u < 3 := by
      have h : p * u < p * 3 := by rw [← hu]; linarith [hZlt]
      exact lt_of_mul_lt_mul_left h (le_of_lt hppos)
    -- u ∈ {1, 2}
    interval_cases u
    · -- u = 1 : Z = p, so W = 3p, contradicts W < 3p
      have hZp : Z = p := by rw [hu]; ring
      have hWval : W = 3 * p := by
        have : p * (Z * W) = p * (3 * p ^ 2) := by rw [hZW]
        nlinarith [hZW, hZp, hWpos, hppos]
      linarith [hWlt, hWval]
    · -- u = 2 : Z = 2p, W*2 = 3p, and 4c = 2p + W
      have hZ2p : Z = 2 * p := by rw [hu]; ring
      -- from Z*W = 3p² and Z = 2p:  2*W = 3*p
      have hW2 : 2 * W = 3 * p := by
        have h1 : (2 * p) * W = 3 * p ^ 2 := by rw [← hZ2p]; exact hZW
        have h2 : p * (2 * W) = p * (3 * p) := by ring_nf; nlinarith [h1]
        have := mul_left_cancel₀ (ne_of_gt hppos) h2
        linarith [this]
      -- 4c = Z + W = 2p + W  ⇒  8c = 4p + 2W = 4p + 3p = 7p
      have h4c : 8 * c = 7 * p := by
        have h : 2 * (4 * c) = 2 * (Z + W) := by rw [h4cZW]
        rw [hZ2p] at h
        linarith [hW2, h]
      -- p ∣ 8c ; p prime, p ∤ c (c < p), so p ∣ 8, forcing p = 2, then 8c = 14 impossible
      have hpdvd8c : p ∣ 8 * c := ⟨7, by linarith [h4c]⟩
      have hcplt : c < p := by rw [hpdef]; exact hcp
      have hcpos : 0 < c := hc
      -- p ∤ c
      have hpndvdc : ¬ p ∣ c := by
        intro ⟨q, hq⟩
        have hqpos : 0 < q := by
          have : 0 < p * q := by rw [← hq]; exact hcpos
          exact (mul_pos_iff_of_pos_left hppos).mp this
        have : p ≤ p * q := le_mul_of_one_le_right (le_of_lt hppos) hqpos
        rw [← hq] at this
        linarith [hcplt, this]
      -- so p ∣ 8
      have hpdvd8 : p ∣ (8 : ℤ) := (hp.dvd_mul.mp hpdvd8c).resolve_right hpndvdc
      -- p is a prime dividing 8 ⇒ p = 2 (argue via `natAbs`, a fresh Nat variable)
      have hp2 : p = 2 := by
        have hpNat : p.natAbs.Prime := Int.prime_iff_natAbs_prime.mp hp
        have hdvdNat : p.natAbs ∣ (8 : ℕ) := by
          have : p.natAbs ∣ (8 : ℤ).natAbs := Int.natAbs_dvd_natAbs.mpr hpdvd8
          simpa using this
        have hle : p.natAbs ≤ 8 := Nat.le_of_dvd (by norm_num) hdvdNat
        have h2le : 2 ≤ p.natAbs := hpNat.two_le
        have hnat2 : p.natAbs = 2 := by
          interval_cases (p.natAbs) <;> first | rfl | (exfalso; revert hpNat hdvdNat; decide)
        have : p = (p.natAbs : ℤ) := (Int.natAbs_of_nonneg (le_of_lt hppos)).symm
        rw [this, hnat2]; norm_num
      -- p = 2 ⇒ 8c = 14 ⇒ no integer solution
      rw [hp2] at h4c
      omega
  -- apply step to whichever of X, Y is divisible by p
  rcases hpX_or_hpY with hpX | hpY
  · exact step X Y hXpos hXlt hYpos hYlt (by linarith [hXY]) hpX (by rw [hXdef, hYdef]; ring)
  · exact step Y X hYpos hYlt hXpos hXlt (by rw [mul_comm]; linarith [hXY]) hpY
      (by rw [hXdef, hYdef]; ring)

/-- **Theorem C (commensurable branch exclusion).** -/
theorem prime_three_mod_four_excluded
    (p : ℕ) (hp : p.Prime) (h4 : p % 4 = 3) (h3 : 3 < p) :
    (¬ IsSquare p) ∧ (¬ ∃ x y : ℕ, x ^ 2 + y ^ 2 = p) ∧
    (¬ ∃ k, p = 2 * k ^ 2) ∧ (¬ ∃ k, p = 3 * k ^ 2) ∧ (¬ ∃ k, p = 6 * k ^ 2) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp_odd : ¬ (2 ∣ p) := by
    intro h2
    have := (hp.eq_one_or_self_of_dvd 2 h2)
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- ¬ IsSquare p : a prime is not a perfect square
    intro ⟨r, hr⟩
    -- p = r * r, prime ⇒ r = 1 or r = p ; either way contradiction with 3 < p
    rcases (hp.eq_one_or_self_of_dvd r ⟨r, hr⟩) with h | h
    · rw [h] at hr; simp at hr; omega
    · -- r = p, then p = p*p ⇒ p*(p-1)=0 ⇒ p ≤ 1
      rw [h] at hr
      have : p * 1 = p * p := by rw [mul_one]; exact hr
      have hpe : (1 : ℕ) = p := Nat.eq_of_mul_eq_mul_left hp.pos this
      omega
  · -- ¬ ∃ sum of two squares : use the prime-factorization characterization
    intro ⟨x, y, hxy⟩
    -- `Nat.eq_sq_add_sq_iff` forces `Even (padicValNat p p)` at the prime `p`, but it is `1`.
    have hforall := Nat.eq_sq_add_sq_iff.mp ⟨x, y, hxy.symm⟩
    have hmem : p ∈ p.primeFactors := hp.mem_primeFactors_self
    have hval : padicValNat p p = 1 := padicValNat_self
    have hEven : Even (padicValNat p p) := hforall p hmem h4
    rw [hval] at hEven
    exact (Nat.not_even_iff_odd.mpr (by decide)) hEven
  · -- ¬ ∃ k, p = 2 k² : p even but p odd
    intro ⟨k, hk⟩
    exact hp_odd ⟨k ^ 2, hk⟩
  · -- ¬ ∃ k, p = 3 k² : 3 ∣ p ⇒ p = 3
    intro ⟨k, hk⟩
    have h3d : 3 ∣ p := ⟨k ^ 2, hk⟩
    have := (hp.eq_one_or_self_of_dvd 3 h3d)
    omega
  · -- ¬ ∃ k, p = 6 k² : p even
    intro ⟨k, hk⟩
    exact hp_odd ⟨3 * k ^ 2, by rw [hk]; ring⟩

end Erdos634

#print axioms Erdos634.k_not_dvd_sum_sub
#print axioms Erdos634.M_not_int
#print axioms Erdos634.iso_reduction_identity
#print axioms Erdos634.add_not_prime
#print axioms Erdos634.prime_three_mod_four_excluded
