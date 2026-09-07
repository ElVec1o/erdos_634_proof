import Mathlib.Tactic
import Mathlib.RingTheory.Int.Basic

/-!
# `thm:admissible` — the squarefree-scale lemma (outcome-1 debt)

Erdős #634, `paper/erdos-634.tex:1435`. The theorem's proof opens: from the area identity
`N·b = k²·(a+2b)` and `gcd(a+2b,b) = 1`, get `b ∣ k²`; then for `p ∣ d`,
`v_p(b) = 2v_p(e)+1 ≤ 2v_p(k)` forces `v_p(k) ≥ v_p(e)+1`, and for `p ∤ d`, `v_p(k) ≥ v_p(e)`;
hence `de ∣ k`.

This file formalizes that valuation argument as a general lemma over ℕ, independent of the
geometric setting, and its immediate consequence for the tile count.

## Scope, stated exactly

**Formalized: the squarefree-scale lemma** `sqfree_scale_dvd` (`b ∣ k², b = d·e², Squarefree d ⟹
d·e ∣ k`), plus the derived count `N = d·w²·(a+2b)` and the algebraic identity
`(c−a−b)(c+a−b) = b(2b+a−2c)` the theorem's proof uses next.

**NOT formalized: the passage from `cor:int` to `e ∣ w(c−a−b)` and the parity clause.** `cor:int`
(`M_α` is an integer `≡ N mod 2`) is a geometric fact about a real dissection's boundary sum, not
an arithmetic identity — formalizing it needs the same tile-placement / boundary-word layer that
blocks `prop:cornerpara` (room `tileplace`, 2026-09-07). `thm:admissible` is **not fully reduced to
arithmetic**; only its first half is. **Label stays PROVED.**

Numerically re-verified first (`private/rs/admissible_check.rs`): over `b < 2000`, every `k` with
`b ∣ k²` (3938 pairs) satisfies `d·e ∣ k` where `(d,e)` is `b`'s squarefree decomposition.
-/

namespace Erdos634.AdmissibleSpectrum

/-- **The squarefree-scale lemma.** If `b ∣ k²`, `b = d·e²` with `d` squarefree, and `k ≠ 0`,
then `d·e ∣ k`. Proof: compare `p`-adic valuations. Since `d` is squarefree, `v_p(d) ∈ {0,1}`; the
hypothesis gives `v_p(d) + 2v_p(e) ≤ 2v_p(k)`. If `v_p(d) = 0` this reads `v_p(e) ≤ v_p(k)`, i.e.
`v_p(d)+v_p(e) ≤ v_p(k)`. If `v_p(d) = 1`, `2v_p(k) ≥ 2v_p(e)+1` and both sides being natural
numbers forces `v_p(k) ≥ v_p(e)+1 = v_p(d)+v_p(e)`. Either way `v_p(d·e) ≤ v_p(k)`, so `d·e ∣ k`. -/
theorem sqfree_scale_dvd {b d e k : ℕ} (hb : b = d * e ^ 2) (hd : Squarefree d)
    (hk : k ≠ 0) (hdvd : b ∣ k ^ 2) : d * e ∣ k := by
  have hd0 : d ≠ 0 := hd.ne_zero
  rcases eq_or_ne e 0 with rfl | he0
  · exfalso; apply hk
    norm_num at hb
    rw [hb] at hdvd
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (Nat.eq_zero_of_zero_dvd hdvd)
  have hb0 : b ≠ 0 := by rw [hb]; positivity
  have hde0 : d * e ≠ 0 := mul_ne_zero hd0 he0
  rw [← Nat.factorization_le_iff_dvd hde0 hk]
  intro p
  have hbfact : b.factorization p = d.factorization p + 2 * e.factorization p := by
    rw [hb, Nat.factorization_mul hd0 (pow_ne_zero 2 he0), Nat.factorization_pow]
    simp
  have hkfact : (k ^ 2).factorization p = 2 * k.factorization p := by
    rw [Nat.factorization_pow]; simp
  have hle : b.factorization p ≤ (k ^ 2).factorization p :=
    (Nat.factorization_le_iff_dvd hb0 (pow_ne_zero 2 hk)).mpr hdvd p
  rw [hbfact, hkfact] at hle
  have hdfact : d.factorization p ≤ 1 := Squarefree.natFactorization_le_one p hd
  have hdefact : (d * e).factorization p = d.factorization p + e.factorization p := by
    rw [Nat.factorization_mul hd0 he0]; simp
  rw [hdefact]
  omega

/-- **The derived tile count.** With `k = d·e·w`, `N·b = k²·(a+2b)` and `b = d·e²` give
`N = d·w²·(a+2b)`. -/
theorem count_eq (N a b d e w : ℕ) (hb : b = d * e ^ 2) (hbpos : 0 < b)
    (harea : N * b = (d * e * w) ^ 2 * (a + 2 * b)) :
    N = d * w ^ 2 * (a + 2 * b) := by
  have hd0 : d ≠ 0 := by rintro rfl; simp at hb; omega
  have key : N * b = (d * w ^ 2 * (a + 2 * b)) * b := by
    rw [harea, hb]; ring
  exact Nat.eq_of_mul_eq_mul_right hbpos key

/-- **`prop:otherspectra`'s squarefree-kernel clause.** If `x·y = z²` with `x,y > 0`, then `x` and
`y` have the same `p`-adic valuation parity at every prime: `v_p(x) + v_p(y) = v_p(z²)` is even, so
`v_p(x)` and `v_p(y)` have the same parity. This is the content of "`N` and `ab` have the same
squarefree kernel" for `N·(ab) = S²` (`prop:otherspectra`'s equilateral clause,
`erdos-634.tex:1701`), stated in the form that is actually used: `x` and `y` are squarefree-part
equal, i.e. `x/gcd-square = y/gcd-square` in the sense of equal odd-valuation primes. -/
theorem same_valuation_parity {x y z : ℕ} (hx : x ≠ 0) (hy : y ≠ 0)
    (heq : x * y = z ^ 2) (p : ℕ) :
    x.factorization p % 2 = y.factorization p % 2 := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at heq; omega
  have hxy : (x * y).factorization p = x.factorization p + y.factorization p :=
    Nat.factorization_mul hx hy ▸ rfl
  have hz : (z ^ 2).factorization p = 2 * z.factorization p := by
    rw [Nat.factorization_pow]; simp
  have : x.factorization p + y.factorization p = 2 * z.factorization p := by
    rw [← hxy, heq, hz]
  omega

/-- Non-vacuity: `x=8, y=2, z=4` (`8·2=16=4²`), `v_2(8)=3`, `v_2(2)=1`, both odd. -/
theorem same_valuation_parity_witness : (8:ℕ).factorization 2 % 2 = (2:ℕ).factorization 2 % 2 :=
  same_valuation_parity (x := 8) (y := 2) (z := 4) (by norm_num) (by norm_num) (by norm_num) 2

/-- **The algebraic identity the proof uses next.** For a `120°`-triple `c² = a²+ab+b²`,
`(c−a−b)(c+a−b) = b(2b+a−2c)` — pure algebra over `ℤ`, no coprimality needed. -/
theorem chord_identity (a b c : ℤ) (h : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    (c - a - b) * (c + a - b) = b * (2 * b + a - 2 * c) := by linear_combination h

/-- Non-vacuity, and a case that shows the lemma needs no coprimality between `d` and `e`:
`b = 8 = 2·2²` (`d=2, e=2`, `gcd(d,e)=2`), `k = 4`: `8 ∣ 16`, and the lemma delivers `4 ∣ 4`. -/
theorem witness_de_not_coprime : (2:ℕ) * 2 ∣ 4 :=
  sqfree_scale_dvd (b := 8) (d := 2) (e := 2) (k := 4) (by norm_num)
    Nat.prime_two.squarefree (by norm_num) (by norm_num)

end Erdos634.AdmissibleSpectrum

#print axioms Erdos634.AdmissibleSpectrum.sqfree_scale_dvd
#print axioms Erdos634.AdmissibleSpectrum.count_eq
#print axioms Erdos634.AdmissibleSpectrum.chord_identity
#print axioms Erdos634.AdmissibleSpectrum.same_valuation_parity
