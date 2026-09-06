import Erdos634.FourCompCongruence
import Erdos634.FCStep1

/-!
# Steps (2) and (3) of the `(2α,α,2β)` chain: from the raw tiling equation to the two branches

Erdős #634.  `FourCompCongruence` proves steps (4) and (5) of the seat's chain and states, in its
own header, that steps (1)–(3) — the passage

    N · R² = M² · A · B        (no divisibility hypothesis on `M`)
      ⟹  A · B = N · w²        (step 2, `v_N`-parity)
      ⟹  (A,B) = (N u², v²)  or  (u², N v²)     (step 3, coprime factorization)

are **not** formalized.  This file closes steps (2) and (3).  Step (1), `gcd(A,B) = 1`, is carried
as an explicit hypothesis `IsCoprime A B` throughout, and is discharged only in the final theorem
`chain_unconditional`, by `Erdos634.FCStep1.gcd_A_B` from the sibling seat.

**Overlap, stated up front.**  `FCStep1.split_of_prime` already proves step (3) *instantiated* at
`A = 2f²−e²`, `B = 3f²−e²`.  `split_of_mul_eq_prime_mul_sq` below is the same statement with `A`,
`B` abstract, proved independently; it is kept because `split_of_raw` needs the abstract form.
**Step (2) — the passage from `N·R² = M²·A·B` to `A·B = N·w²` — is in neither `FCStep1` nor
anywhere else in `lean/`;** it is the new content here.

`A` and `B` are kept abstract: nothing below knows they are `2f²−e²` and `3f²−e²`.  Positivity
(`0 < A`, `0 < B`) is carried as a hypothesis rather than fighting the `±` cases of
`Int.sq_of_isCoprime`; it is discharged for the intended `A`, `B` by `A_pos` / `B_pos` at the
bottom, from `0 < e < f`.

## What is proved

* `sq_dvd_prime_eq_one` / `int_sq_dvd_prime` — a prime is not divisible by a nontrivial square.
* `mul_eq_prime_mul_sq_of_raw`  — **step (2)**.  `N·R² = M²·A·B`, `M ≠ 0`, `N` prime  ⟹  `∃ w, A·B = N·w²`.
  Proof: pull `g = gcd(M,R)` out of both sides, `M = m g`, `R = r g`, cancel `g²`, get
  `N r² = m² (AB)`; `m² ∣ N r²` and `gcd(m,r) = 1` give `m² ∣ N`, so `m² = 1`.
  This replaces the `v_N`-parity argument by a two-line gcd argument, and needs no positivity.
* `split_of_mul_eq_prime_mul_sq` — **step (3)**.  `A·B = N·w²`, `IsCoprime A B`, `0<A`, `0<B`,
  `N` prime ⟹ the two branches.
* `split_of_raw` — (2)+(3) composed: the target of this seat.
* `fourcomp_prime_eq_two_raw` — (2)+(3) composed with `FourCompCongruence.fourcomp_no_odd_prime`:
  from the raw equation at `A = 2f²−e²`, `B = 3f²−e²`, with `gcd(A,B)=1` assumed, `N` prime
  forces `N = 2`.  Beeson's Theorem 11 is nowhere in the chain.
* `chain_unconditional` — the same with step (1) discharged by `FCStep1.gcd_A_B`, so the only
  remaining hypotheses are `gcd(e,f) = 1`, `0 < e < f`, `M ≠ 0`, `N` prime, and the raw equation.

## Honest scope

Witnesses satisfying every hypothesis of the abstract theorems are exhibited and
typechecked in the `Witness` section — including one that fires each branch — so nothing below is
vacuous.  The *instantiated* corollary `fourcomp_prime_eq_two_raw` is an exclusion statement: its
hypotheses are not known to be satisfiable at any `(e,f)`, which is its content, not a defect.
-/

namespace Erdos634.FCStep2

/-! ### A prime has no nontrivial square divisor -/

/-- If `a² ∣ N` with `N` prime then `a = 1`. -/
theorem sq_dvd_prime_eq_one {a N : ℕ} (hN : N.Prime) (h : a ^ 2 ∣ N) : a = 1 := by
  have ha : a ∣ N := dvd_trans (dvd_pow_self a two_ne_zero) h
  rcases hN.eq_one_or_self_of_dvd a ha with h1 | h1
  · exact h1
  · rw [h1] at h
    have hle := Nat.le_of_dvd hN.pos h
    nlinarith [hN.two_le]

/-- Integer form: `m² ∣ (N : ℤ)` with `N` prime forces `m² = 1`. -/
theorem int_sq_dvd_prime {m : ℤ} {N : ℕ} (hN : N.Prime) (h : m ^ 2 ∣ (N : ℤ)) : m ^ 2 = 1 := by
  have h0 : (m ^ 2).natAbs ∣ ((N : ℤ)).natAbs := Int.natAbs_dvd_natAbs.mpr h
  rw [Int.natAbs_pow, Int.natAbs_natCast] at h0
  have h1 : m.natAbs = 1 := sq_dvd_prime_eq_one hN h0
  rcases Int.natAbs_eq m with hm | hm <;> rw [hm, h1] <;> norm_num

/-! ### Step (2): the raw equation yields `A·B = N·w²` -/

/-- **Step (2).**  From the raw tiling equation `N·R² = M²·A·B`, with `N` prime and `M ≠ 0` and
**no** divisibility hypothesis on `M`, the product `A·B` is `N` times a square.

The `v_N`-parity argument is replaced by a gcd extraction: writing `g = gcd(M,R)`, `M = m·g`,
`R = r·g` with `gcd(m,r) = 1`, cancelling `g²` gives `N·r² = m²·(A·B)`, so `m² ∣ N·r²`; coprimality
gives `m² ∣ N`, and a prime carries no nontrivial square divisor, so `m² = 1`. -/
theorem mul_eq_prime_mul_sq_of_raw {A B M R : ℤ} {N : ℕ} (hN : N.Prime) (hM : M ≠ 0)
    (h : (N : ℤ) * R ^ 2 = M ^ 2 * A * B) : ∃ w : ℤ, A * B = (N : ℤ) * w ^ 2 := by
  have hgpos : 0 < Int.gcd M R := Int.gcd_pos_iff.mpr (Or.inl hM)
  obtain ⟨g, m, r, hg0, hcop, hMe, hRe⟩ := Int.exists_gcd_one' hgpos
  have hgne : ((g : ℤ)) ≠ 0 := by exact_mod_cast hg0.ne'
  -- cancel `g²`
  have hcancel : ((g : ℤ)) ^ 2 * ((N : ℤ) * r ^ 2) = ((g : ℤ)) ^ 2 * (m ^ 2 * (A * B)) := by
    rw [hMe, hRe] at h; ring_nf; ring_nf at h; linarith [h]
  have hkey : (N : ℤ) * r ^ 2 = m ^ 2 * (A * B) :=
    mul_left_cancel₀ (pow_ne_zero 2 hgne) hcancel
  -- `m² ∣ N`
  have hcopI : IsCoprime m r := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have hcop2 : IsCoprime (m ^ 2) (r ^ 2) := hcopI.pow
  have hdvd : m ^ 2 ∣ (N : ℤ) * r ^ 2 := ⟨A * B, hkey⟩
  have hm1 : m ^ 2 = 1 := int_sq_dvd_prime hN (hcop2.dvd_of_dvd_mul_right hdvd)
  exact ⟨r, by rw [hm1, one_mul] at hkey; exact hkey.symm⟩

/-! ### Step (3): the coprime split -/

/-- A positive integer that is `± a square` is that square. -/
private theorem pos_of_sq_or_neg_sq {x a : ℤ} (hx : 0 < x) (h : x = a ^ 2 ∨ x = -a ^ 2) :
    x = a ^ 2 := by
  rcases h with h | h
  · exact h
  · exfalso; nlinarith [sq_nonneg a]

/-- **Step (3).**  If `A·B = N·w²` with `A`, `B` coprime and positive and `N` prime, then `N`
attaches to exactly one of them and the other factor is a square. -/
theorem split_of_mul_eq_prime_mul_sq {A B w : ℤ} {N : ℕ} (hN : N.Prime)
    (hAB : IsCoprime A B) (hA : 0 < A) (hB : 0 < B) (h : A * B = (N : ℤ) * w ^ 2) :
    (∃ u v : ℤ, A = (N : ℤ) * u ^ 2 ∧ B = v ^ 2) ∨
    (∃ u v : ℤ, A = u ^ 2 ∧ B = (N : ℤ) * v ^ 2) := by
  have hNp : Prime ((N : ℤ)) := Nat.prime_iff_prime_int.mp hN
  have hN0 : ((N : ℤ)) ≠ 0 := hNp.ne_zero
  have hNpos : (0 : ℤ) < (N : ℤ) := by exact_mod_cast hN.pos
  have hdvd : ((N : ℤ)) ∣ A * B := ⟨w ^ 2, h⟩
  rcases (hNp.dvd_mul).mp hdvd with hdA | hdB
  · -- `N ∣ A`
    obtain ⟨A₁, hA₁⟩ := hdA
    have hA₁pos : 0 < A₁ := by nlinarith [hA, hNpos]
    have hsq : A₁ * B = w ^ 2 := by
      have : (N : ℤ) * (A₁ * B) = (N : ℤ) * w ^ 2 := by rw [hA₁] at h; linarith [h]
      exact mul_left_cancel₀ hN0 this
    have hcop1 : IsCoprime A₁ B := hAB.of_isCoprime_of_dvd_left ⟨(N : ℤ), by rw [hA₁]; ring⟩
    obtain ⟨u, hu⟩ := Int.sq_of_isCoprime hcop1 hsq
    obtain ⟨v, hv⟩ := Int.sq_of_isCoprime hcop1.symm (by rw [mul_comm]; exact hsq)
    exact Or.inl ⟨u, v, by rw [hA₁, pos_of_sq_or_neg_sq hA₁pos hu], pos_of_sq_or_neg_sq hB hv⟩
  · -- `N ∣ B`
    obtain ⟨B₁, hB₁⟩ := hdB
    have hB₁pos : 0 < B₁ := by nlinarith [hB, hNpos]
    have hsq : A * B₁ = w ^ 2 := by
      have : (N : ℤ) * (A * B₁) = (N : ℤ) * w ^ 2 := by rw [hB₁] at h; linarith [h]
      exact mul_left_cancel₀ hN0 this
    have hcop1 : IsCoprime A B₁ := hAB.of_isCoprime_of_dvd_right ⟨(N : ℤ), by rw [hB₁]; ring⟩
    obtain ⟨u, hu⟩ := Int.sq_of_isCoprime hcop1 hsq
    obtain ⟨v, hv⟩ := Int.sq_of_isCoprime hcop1.symm (by rw [mul_comm]; exact hsq)
    exact Or.inr ⟨u, v, pos_of_sq_or_neg_sq hA hu, by rw [hB₁, pos_of_sq_or_neg_sq hB₁pos hv]⟩

/-! ### (2) + (3): the seat's target -/

/-- **Steps (2) and (3) composed.**  From the raw tiling equation `N·R² = M²·A·B` — with no
divisibility hypothesis on `M` — together with `N` prime, `gcd(A,B) = 1` and `A, B > 0`, the pair
`(A,B)` is `(N u², v²)` or `(u², N v²)`. -/
theorem split_of_raw {A B M R : ℤ} {N : ℕ} (hN : N.Prime) (hAB : IsCoprime A B)
    (hA : 0 < A) (hB : 0 < B) (hM : M ≠ 0) (h : (N : ℤ) * R ^ 2 = M ^ 2 * A * B) :
    (∃ u v : ℤ, A = (N : ℤ) * u ^ 2 ∧ B = v ^ 2) ∨
    (∃ u v : ℤ, A = u ^ 2 ∧ B = (N : ℤ) * v ^ 2) := by
  obtain ⟨w, hw⟩ := mul_eq_prime_mul_sq_of_raw hN hM h
  exact split_of_mul_eq_prime_mul_sq hN hAB hA hB hw

/-! ### The intended `A`, `B`, and the chain to `N = 2` -/

/-- `A = 2f² − e² > 0` for `0 < e < f`. -/
theorem A_pos {e f : ℤ} (he : 0 < e) (hef : e < f) : 0 < 2 * f ^ 2 - e ^ 2 := by nlinarith

/-- `B = 3f² − e² > 0` for `0 < e < f`. -/
theorem B_pos {e f : ℤ} (he : 0 < e) (hef : e < f) : 0 < 3 * f ^ 2 - e ^ 2 := by nlinarith

/-- **The chain, from the raw equation.**  With step (1) (`gcd(A,B) = 1`) supplied as a hypothesis,
the raw tiling equation `N·R² = M²·A·B` at `A = 2f²−e²`, `B = 3f²−e²` forces `N = 2` for `N` prime.
Beeson's (misprinted) Theorem 11 is not used anywhere in the chain. -/
theorem fourcomp_prime_eq_two_raw {e f M R : ℤ} {N : ℕ}
    (hc : IsCoprime e f) (hN : N.Prime) (he : 0 < e) (hef : e < f)
    (hABcop : IsCoprime (2 * f ^ 2 - e ^ 2) (3 * f ^ 2 - e ^ 2)) (hM : M ≠ 0)
    (h : (N : ℤ) * R ^ 2 = M ^ 2 * (2 * f ^ 2 - e ^ 2) * (3 * f ^ 2 - e ^ 2)) : N = 2 :=
  Erdos634.FourCompCongruence.fourcomp_no_odd_prime hc hN
    (split_of_raw hN hABcop (A_pos he hef) (B_pos he hef) hM h)

/-! ### Witnesses

Every hypothesis of the abstract theorems is satisfiable, and both branches of the conclusion
occur.  These are typechecked, not asserted. -/

section Witness

/-- Branch-one witness for `split_of_raw`: `N = 3`, `A = 3`, `B = 4`, `M = 1`, `R = 2`.
`3·2² = 1²·3·4`, `gcd(3,4) = 1`, and the conclusion fires as `A = 3·1²`, `B = 2²`. -/
theorem witness_branch_one :
    (3 : ℕ).Prime ∧ IsCoprime (3 : ℤ) (4 : ℤ) ∧ (0 : ℤ) < 3 ∧ (0 : ℤ) < 4 ∧ (1 : ℤ) ≠ 0 ∧
      ((3 : ℕ) : ℤ) * (2 : ℤ) ^ 2 = (1 : ℤ) ^ 2 * (3 : ℤ) * (4 : ℤ) :=
  ⟨by norm_num, ⟨-1, 1, by norm_num⟩, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The branch-one witness really produces the left disjunct. -/
example : (∃ u v : ℤ, (3 : ℤ) = ((3 : ℕ) : ℤ) * u ^ 2 ∧ (4 : ℤ) = v ^ 2) ∨
    (∃ u v : ℤ, (3 : ℤ) = u ^ 2 ∧ (4 : ℤ) = ((3 : ℕ) : ℤ) * v ^ 2) :=
  split_of_raw (M := 1) (R := 2) (by norm_num) ⟨-1, 1, by norm_num⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Branch-two witness: `N = 3`, `A = 4`, `B = 3`, `M = 5`, `R = 10`.  `3·10² = 5²·4·3`, and `M ≠ 1`
so the `g = gcd(M,R)` extraction in step (2) is exercised nontrivially (`g = 5`, `m = 1`, `r = 2`). -/
theorem witness_branch_two :
    ((3 : ℕ) : ℤ) * (10 : ℤ) ^ 2 = (5 : ℤ) ^ 2 * (4 : ℤ) * (3 : ℤ) := by norm_num

example : (∃ u v : ℤ, (4 : ℤ) = ((3 : ℕ) : ℤ) * u ^ 2 ∧ (3 : ℤ) = v ^ 2) ∨
    (∃ u v : ℤ, (4 : ℤ) = u ^ 2 ∧ (3 : ℤ) = ((3 : ℕ) : ℤ) * v ^ 2) :=
  split_of_raw (M := 5) (R := 10) (by norm_num) ⟨1, -1, by norm_num⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **The real-`A`,`B` witness for step (3).**  `e = 647`, `f = 2993` (coprime, `0 < e < f`) gives
`A = 2f²−e² = 17497489 = 4183²` and `B = 3f²−e² = 26455538 = 2·3637²`, so
`A·B = 2·(4183·3637)² = 2·15213571²` with `N = 2` prime and `gcd(A,B) = 1`
(Bézout: `144093·A − 95302·B = 1`).  This is the unique coprime pair with `f < 3000` for which
`A·B` is a prime times a square.  Every hypothesis of `split_of_mul_eq_prime_mul_sq` holds here. -/
theorem witness_647_2993_hyps :
    (2 * (2993 : ℤ) ^ 2 - (647 : ℤ) ^ 2 = 17497489) ∧
    (3 * (2993 : ℤ) ^ 2 - (647 : ℤ) ^ 2 = 26455538) ∧
    IsCoprime (17497489 : ℤ) (26455538 : ℤ) ∧
    (0 : ℤ) < 17497489 ∧ (0 : ℤ) < 26455538 ∧
    (17497489 : ℤ) * 26455538 = ((2 : ℕ) : ℤ) * (15213571 : ℤ) ^ 2 :=
  ⟨by norm_num, by norm_num, ⟨144093, -95302, by norm_num⟩,
   by norm_num, by norm_num, by norm_num⟩

/-- and step (3) fires on it. -/
example : (∃ u v : ℤ, (17497489 : ℤ) = ((2 : ℕ) : ℤ) * u ^ 2 ∧ (26455538 : ℤ) = v ^ 2) ∨
    (∃ u v : ℤ, (17497489 : ℤ) = u ^ 2 ∧ (26455538 : ℤ) = ((2 : ℕ) : ℤ) * v ^ 2) :=
  split_of_mul_eq_prime_mul_sq (w := 15213571) (by norm_num) ⟨144093, -95302, by norm_num⟩
    (by norm_num) (by norm_num) (by norm_num)

/-- Which disjunct, checked rather than asserted: at `e = 647`, `f = 2993` it is the **second**
branch, `A = 4183²` and `B = 2·3637²`. -/
theorem witness_647_2993_is_branch_two :
    (17497489 : ℤ) = (4183 : ℤ) ^ 2 ∧ (26455538 : ℤ) = ((2 : ℕ) : ℤ) * (3637 : ℤ) ^ 2 := by
  norm_num

/-- And the small witnesses land where claimed: `3 = 3·1²`, `4 = 2²` (branch one);
`4 = 2²`, `3 = 3·1²` (branch two). -/
theorem witness_small_branches :
    ((3 : ℤ) = ((3 : ℕ) : ℤ) * (1 : ℤ) ^ 2 ∧ (4 : ℤ) = (2 : ℤ) ^ 2) ∧
    ((4 : ℤ) = (2 : ℤ) ^ 2 ∧ (3 : ℤ) = ((3 : ℕ) : ℤ) * (1 : ℤ) ^ 2) := by
  norm_num

end Witness

/-- **The chain with step (1) discharged.**  `FCStep1.gcd_A_B` (a sibling seat's file, read and
re-checked here: `e² = 2B − 3A`, `f² = B − A`, so a Bézout pair for `(e²,f²)` gives one for `(A,B)`)
supplies `IsCoprime A B`.  Composing, the raw tiling equation

    N · R² = M² · (2f²−e²) · (3f²−e²),   M ≠ 0,   gcd(e,f) = 1,   0 < e < f,   N prime

forces `N = 2` — with **no** divisibility hypothesis on `M` and with Beeson's misprinted Theorem 11
nowhere in the chain.  The only external input is `FCStep1.gcd_A_B`. -/
theorem chain_unconditional {e f M R : ℤ} {N : ℕ}
    (hc : IsCoprime e f) (hN : N.Prime) (he : 0 < e) (hef : e < f) (hM : M ≠ 0)
    (h : (N : ℤ) * R ^ 2 = M ^ 2 * (2 * f ^ 2 - e ^ 2) * (3 * f ^ 2 - e ^ 2)) : N = 2 :=
  fourcomp_prime_eq_two_raw hc hN he hef (Erdos634.FCStep1.gcd_A_B hc) hM h

end Erdos634.FCStep2

#print axioms Erdos634.FCStep2.chain_unconditional
#print axioms Erdos634.FCStep2.mul_eq_prime_mul_sq_of_raw
#print axioms Erdos634.FCStep2.split_of_mul_eq_prime_mul_sq
#print axioms Erdos634.FCStep2.split_of_raw
#print axioms Erdos634.FCStep2.fourcomp_prime_eq_two_raw
#print axioms Erdos634.FCStep2.witness_647_2993_hyps
