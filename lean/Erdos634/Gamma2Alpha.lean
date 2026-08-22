import Mathlib.Tactic
import Mathlib.RingTheory.IntegralDomain
import Mathlib.Data.Nat.GCD.Basic

/-!
The `γ = 2α` tile parametrization as pure number theory (Beeson, *Tilings of an isosceles
triangle*, Lemma 11.2), proved here with no tiling theory and no dependence on any preprint.

If `(a,b,c)` are the integer sides, with no common factor, of a triangle whose angles satisfy
`γ = 2α` — equivalently `c^2 = a^2 + a*b` by the law of cosines — then `(a,b,c) = (k^2, m^2-k^2, k*m)`
for coprime `k < m`.  This is the arithmetic content that turns the `γ = 2α` branch into a finite,
decidable search; formalizing it removes that branch's tile classification from any citation.
-/

theorem gamma2alpha_param (a b c : ℕ) (hb : 0 < b)
    (hc : c ^ 2 = a ^ 2 + a * b) (hcop : Nat.gcd (Nat.gcd a b) c = 1) :
    ∃ k m : ℕ, Nat.Coprime k m ∧ k < m ∧ a = k ^ 2 ∧ b = m ^ 2 - k ^ 2 ∧ c = k * m := by
  have hcab : c ^ 2 = a * (a + b) := by rw [hc]; ring
  -- g := gcd a b divides a, b, a+b, and (via g^2 ∣ c^2) divides c; with gcd(g,c)=1, g = 1.
  set g := Nat.gcd a b with hg
  have hga : g ∣ a := Nat.gcd_dvd_left a b
  have hgb : g ∣ b := Nat.gcd_dvd_right a b
  have hg2c2 : g ^ 2 ∣ c ^ 2 := by
    rw [hcab, pow_two]; exact mul_dvd_mul hga (Nat.dvd_add hga hgb)
  have hgc : g ∣ c := (Nat.pow_dvd_pow_iff (by norm_num)).mp hg2c2
  have hg1 : g = 1 := by rw [← Nat.gcd_eq_left hgc]; exact hcop
  have hcopab : Nat.Coprime a b := hg1
  have hcopab' : Nat.Coprime a (a + b) := by
    rw [add_comm]; exact (Nat.coprime_add_self_right).mpr hcopab
  -- a and a+b are coprime factors of the square c^2, so each is itself a square (ℕ, Subsingleton ℕˣ)
  have hsq : a * (a + b) = c ^ 2 := hcab.symm
  have hua : IsUnit (gcd a (a + b)) := by
    rw [Nat.isUnit_iff]; exact hcopab'
  have hub : IsUnit (gcd (a + b) a) := by
    rw [Nat.isUnit_iff]; exact hcopab'.symm
  obtain ⟨k, hk⟩ := exists_eq_pow_of_mul_eq_pow hua hsq
  obtain ⟨m, hm⟩ := exists_eq_pow_of_mul_eq_pow hub (by rw [mul_comm]; exact hsq)
  have hkn : a = k ^ 2 := hk
  have hmn : a + b = m ^ 2 := hm
  -- k < m from a = k^2 < m^2 = a+b (b > 0)
  have hlt : k ^ 2 < m ^ 2 := by omega
  have hkm : k < m := by
    by_contra h; push_neg at h; have := Nat.pow_le_pow_left h 2; omega
  -- coprime k m from coprime k^2 m^2
  have hcopkm : Nat.Coprime k m := by
    have h2 : Nat.Coprime (k ^ 2) (m ^ 2) := by rw [← hkn, ← hmn]; exact hcopab'
    exact Nat.Coprime.coprime_dvd_right (dvd_pow_self m two_ne_zero)
      (Nat.Coprime.coprime_dvd_left (dvd_pow_self k two_ne_zero) h2)
  -- c = k*m from c^2 = a*(a+b) = k^2*m^2
  have hceq : c = k * m := by
    have : c ^ 2 = (k * m) ^ 2 := by rw [hcab, hmn, hkn]; ring
    exact Nat.pow_left_injective (by norm_num) this
  exact ⟨k, m, hcopkm, hkm, hkn, by omega, hceq⟩

#print axioms gamma2alpha_param
