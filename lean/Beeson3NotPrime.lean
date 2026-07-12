import Mathlib.Tactic

/-!
"No prime `N` when `3α+2β=π`" — the arithmetic core of Beeson III (*Triangle tiling: the case
3α+2β=π*, Theorem 8), re-proved here from scratch with no tiling theory and no dependence on the
preprint.

For the target shape `(2α, β, α+β)` Beeson's first tiling equation is `N + M² = 2K²` with the
coloring number `M`, the side-ratio datum `K`, and the divisibility `K ∣ N` (from `K ∣ M²`).
Given only that Diophantine datum, the theorem below shows an **odd prime** `N` is impossible:
`K ∣ N` forces `K ∈ {1, N}`; `K = 1` gives `N ≤ 2`, and `K = N` gives `M² = N(2N−1)`, whence
`N ∣ M`, `N·t² + 1 = 2N`, and `N ∣ 1`. This is the exclusion the companion paper's prime dichotomy
cites Beeson III for; the step "tiling equation ⟹ not prime" is now machine-checked. Axiom-clean.
-/

namespace Erdos634.Beeson3

/-- Beeson III, Theorem 8 (arithmetic core): if the first tiling equation `N + M² = 2K²` holds with
`K ∣ N`, then `N` is not an odd prime.  Hence the `(2α,β,α+β)` branch of `3α+2β=π` contributes no
prime tile count. -/
theorem triquadratic_not_prime (N K M : ℕ) (hN : N.Prime) (hodd : Odd N)
    (hK : K ∣ N) (heq : N + M ^ 2 = 2 * K ^ 2) : False := by
  have hN3 : 3 ≤ N := by
    rcases hN.two_le.eq_or_lt with h | h
    · rw [← h] at hodd; exact absurd hodd (by decide)
    · omega
  rcases hN.eq_one_or_self_of_dvd K hK with h1 | hNK
  · -- K = 1 : N + M² = 2, impossible for N ≥ 3
    subst h1; nlinarith [Nat.zero_le (M ^ 2), heq]
  · -- K = N
    rw [hNK] at heq
    have hNpos : 0 < N := hN.pos
    have heqZ : (N : ℤ) + (M : ℤ) ^ 2 = 2 * (N : ℤ) ^ 2 := by exact_mod_cast heq
    have hdvd : N ∣ M ^ 2 := by
      have : (N : ℤ) ∣ (M : ℤ) ^ 2 := ⟨2 * N - 1, by nlinarith [heqZ]⟩
      exact_mod_cast this
    obtain ⟨t, ht⟩ := hN.dvd_of_dvd_pow hdvd
    subst ht
    have hkey : 1 + N * t ^ 2 = 2 * N :=
      Nat.eq_of_mul_eq_mul_left hNpos (by nlinarith [heq])
    have ht2 : t ^ 2 < 2 := by nlinarith [hkey, hN3]
    have ht1 : t < 2 := by
      by_contra h; rw [not_lt] at h; nlinarith [ht2, h]
    interval_cases t <;> omega

/-- Four-component `(2α,α,2β)` target (Beeson III, Theorem 12): the second tiling equation
`N/M² = (2−s²)(3−s²)/((1−s)²(2+s)²)` with `s = e/f` and `(f−e)(2f+e) ∣ M` forces the tile count to
the shape `N = (2f²−e²)(3f²−e²)k²` (`k = M/((f−e)(2f+e))`).  Every such `N` is composite: for
`1 ≤ e < f` both factors satisfy `2f²−e² ≥ 7` and `3f²−e² ≥ 11`, so `N` is a product of two integers
`> 1`.  Hence no four-component `3α+2β` tiling has prime `N`.  (E.g.\ `(2,3,4)→77=7·11`,
`(3,8,9)→442=17·26`.) -/
theorem fourcomp_not_prime (e f k : ℕ) (he : 1 ≤ e) (hef : e < f) (hk : 1 ≤ k) :
    ¬ ((2 * f ^ 2 - e ^ 2) * ((3 * f ^ 2 - e ^ 2) * k ^ 2)).Prime := by
  have hf : 2 ≤ f := by omega
  have hAe : e ^ 2 + 2 ≤ 2 * f ^ 2 := by nlinarith [hef, he, hf]
  have hBe : e ^ 2 + 2 ≤ 3 * f ^ 2 := by nlinarith [hef, he, hf]
  have hA : 2 ≤ 2 * f ^ 2 - e ^ 2 := by omega
  have hB : 2 ≤ 3 * f ^ 2 - e ^ 2 := by omega
  have hk2 : 1 ≤ k ^ 2 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (by omega))
  have hBk : 2 ≤ (3 * f ^ 2 - e ^ 2) * k ^ 2 :=
    le_trans hB (Nat.le_mul_of_pos_right _ (by omega))
  intro hp
  have hdvd : (2 * f ^ 2 - e ^ 2) ∣ (2 * f ^ 2 - e ^ 2) * ((3 * f ^ 2 - e ^ 2) * k ^ 2) :=
    Dvd.intro _ rfl
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | hself
  · omega
  · nlinarith [hself, hA, hBk]

end Erdos634.Beeson3

#print axioms Erdos634.Beeson3.triquadratic_not_prime
#print axioms Erdos634.Beeson3.fourcomp_not_prime
