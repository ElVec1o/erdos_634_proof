import Mathlib.Tactic

/-!
"No prime `N` when `ABC` is isosceles with base angles `α`" (the `3α+2β=π` branch) — a **correct
replacement** for Beeson III, Theorem 20, whose proof depends on Theorem 19's `g ∣ M`, itself
unsound as printed (its equation (34) bookkeeping asserts `bc³(a+c)` is not divisible by `g⁵`, but
with `c = g²` it carries `g⁷` identically; moreover the squarefree half of Lemma 8, which the
`g ∣ M` proofs invoke, is false — counterexample tile `(4,15,16)` with `g = 4`).

The replacement needs **no** `g ∣ M`.  With `s = e/f` in lowest terms the tile is
`(ef, f²−e², f²)`, and two necessary conditions of an `N`-tiling suffice:

* the Theorem-19 tiling equation `N(f−e)(2f+e)² = M²(f+e)(2f²−e²)`, and
* integrality of the equal side `X` (`X² = Nbc/(2−s²)`), which resolves to
  `X·(2f+e) = M(f+e)f²` and hence — `2f+e` being coprime to both `f` and `f+e` — to
  `(2f+e) ∣ M` (`isoalpha_X_forces`).

Substituting `M = (2f+e)m` reduces the equation to `N(f−e) = m²(f+e)(2f²−e²)`.  Writing `d = f−e`
and `Q = 2f²−e² = e²+4ed+2d²`, `gcd(d,Q) = 1`, so the minimal prime factor of `Q` divides `N`,
i.e. `N ∣ Q`; cancelling `N` leaves `d = m²(2e+d)(Q/N) ≥ 2e+d`, absurd (`isoalpha_not_prime`).
Axiom-clean; the geometric inputs (tiling equation, whole-edge side partition) are the sound half
of Beeson's Theorem 19, cited not formalized.
-/

namespace Erdos634.IsoAlpha

/-- Side-integrality pillar: `X·(2f+e) = M·(f+e)·f²` with `gcd(e,f) = 1` forces `(2f+e) ∣ M`,
since `2f+e` is coprime to both `f` and `f+e`. -/
theorem isoalpha_X_forces (e f M X : ℕ) (hcop : Nat.Coprime e f)
    (hX : X * (2 * f + e) = M * ((f + e) * f ^ 2)) : (2 * f + e) ∣ M := by
  have hgef : Nat.gcd e f = 1 := hcop
  have hcop1 : Nat.Coprime (2 * f + e) f := by
    by_contra h
    obtain ⟨p, hp, hp1, hp2⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
    have hpe : p ∣ e := (Nat.dvd_add_right (hp2.mul_left 2)).mp hp1
    have hg : p ∣ Nat.gcd e f := Nat.dvd_gcd hpe hp2
    rw [hgef, Nat.dvd_one] at hg
    exact hp.one_lt.ne' hg
  have hcop2 : Nat.Coprime (2 * f + e) (f + e) := by
    by_contra h
    obtain ⟨p, hp, hp1, hp2⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
    have hsplit : 2 * f + e = (f + e) + f := by ring
    rw [hsplit] at hp1
    have hpf : p ∣ f := (Nat.dvd_add_right hp2).mp hp1
    have hpe : p ∣ e := (Nat.dvd_add_right hpf).mp hp2
    have hg : p ∣ Nat.gcd e f := Nat.dvd_gcd hpe hpf
    rw [hgef, Nat.dvd_one] at hg
    exact hp.one_lt.ne' hg
  have hdvd : (2 * f + e) ∣ M * ((f + e) * f ^ 2) := ⟨X, by rw [← hX]; ring⟩
  exact (hcop2.mul_right (hcop1.pow_right 2)).dvd_of_dvd_mul_right hdvd

/-- Main pillar: no **prime** `N` satisfies the reduced base-`α` system.  Subtraction-free data:
`d = f−e ≥ 1` (so `f = e+d`, `f+e = 2e+d`) and `Q = e²+4ed+2d²` (`= 2f²−e²`).  The reduced tiling
equation `N·d = m²·((2e+d)·Q)` is impossible: `gcd(d,Q) = 1` forces `N ∣ Q`, and cancelling `N`
gives `d ≥ 2e+d`. -/
theorem isoalpha_not_prime (N e d m : ℕ) (hN : N.Prime) (he : 1 ≤ e) (hd : 1 ≤ d)
    (hcop : Nat.Coprime e (e + d))
    (heq : N * d = m ^ 2 * ((2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2))) : False := by
  set Q := e ^ 2 + 4 * e * d + 2 * d ^ 2 with hQdef
  have hged : Nat.gcd e (e + d) = 1 := hcop
  -- gcd(d, Q) = 1: a common prime would divide e² (Q = d·(4e+2d) + e²), hence e, hence e+d, hence 1
  have hdQ : Nat.gcd d Q = 1 := by
    by_contra h
    obtain ⟨p, hp, hp1, hp2⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
    have hQr : Q = d * (4 * e + 2 * d) + e ^ 2 := by rw [hQdef]; ring
    rw [hQr] at hp2
    have hpe2 : p ∣ e ^ 2 := (Nat.dvd_add_right (hp1.mul_right _)).mp hp2
    have hpe : p ∣ e := hp.dvd_of_dvd_pow hpe2
    have hped : p ∣ e + d := Nat.dvd_add hpe hp1
    have hg : p ∣ Nat.gcd e (e + d) := Nat.dvd_gcd hpe hped
    rw [hged, Nat.dvd_one] at hg
    exact hp.one_lt.ne' hg
  -- Q ≥ 7, so it has a prime factor q; q ∤ d, q ∣ N·d ⟹ q = N ⟹ N ∣ Q
  have hQ7 : 7 ≤ Q := by rw [hQdef]; nlinarith [he, hd]
  have hqp : (Nat.minFac Q).Prime := Nat.minFac_prime (by omega)
  have hqQ : Nat.minFac Q ∣ Q := Nat.minFac_dvd Q
  have hqNd : Nat.minFac Q ∣ N * d := by
    rw [heq]
    exact Dvd.dvd.mul_left (hqQ.mul_left (2 * e + d)) (m ^ 2)
  have hqnd : ¬ Nat.minFac Q ∣ d := by
    intro h
    have hg : Nat.minFac Q ∣ Nat.gcd d Q := Nat.dvd_gcd h hqQ
    rw [hdQ, Nat.dvd_one] at hg
    exact hqp.one_lt.ne' hg
  have hqN : Nat.minFac Q ∣ N := by
    rcases (Nat.Prime.dvd_mul hqp).mp hqNd with h | h
    · exact h
    · exact absurd h hqnd
  have hNQ : N ∣ Q := (Nat.prime_dvd_prime_iff_eq hqp hN).mp hqN ▸ hqQ
  obtain ⟨Q1, hQ1eq⟩ := hNQ
  -- cancel N: d = m²·(2e+d)·Q1, then d ≥ 2e+d, absurd
  have hcancel : N * d = N * (m ^ 2 * ((2 * e + d) * Q1)) := by
    rw [heq, hQ1eq]; ring
  have hdval : d = m ^ 2 * ((2 * e + d) * Q1) := Nat.eq_of_mul_eq_mul_left hN.pos hcancel
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp at hdval; omega
    · exact h
  have hQ1p : 1 ≤ Q1 := by
    rcases Nat.eq_zero_or_pos Q1 with rfl | h
    · simp at hdval; omega
    · exact h
  have hge : 2 * e + d ≤ d := by
    calc 2 * e + d = (2 * e + d) * 1 := by ring
    _ ≤ (2 * e + d) * (m ^ 2 * Q1) := by
        exact Nat.mul_le_mul_left _ (Nat.one_le_iff_ne_zero.mpr (by positivity))
    _ = m ^ 2 * ((2 * e + d) * Q1) := by ring
    _ = d := hdval.symm
  omega

end Erdos634.IsoAlpha

#print axioms Erdos634.IsoAlpha.isoalpha_X_forces
#print axioms Erdos634.IsoAlpha.isoalpha_not_prime
