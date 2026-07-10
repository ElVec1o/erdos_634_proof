import Mathlib.Tactic
import Mathlib.NumberTheory.SumTwoSquares

/-!
# Erdős Problem #634 — the arithmetic layer of the Φ-invariant proof

For a primitive 120°-triple `(a, b, c)` (`gcd = 1`, `c² = a² + ab + b²`) whose squared leg is
`b = k²`, the integer `k` does **not** divide `a + b − c`.  Equivalently the Φ-invariant tile-count
`M = (c − a − b)/k` is never an integer, so no prime number of `2π/3` tiles tiles an isosceles
triangle; with the composite tile counts of the scalene families and the exclusion of the
commensurable-angle forms this resolves the conjecture that no prime `≡ 3 (mod 4)` exceeding `3`
is achievable (`3` itself occurs, in the commensurable branch) — Erdős #634, prime case.

This file machine-checks the **arithmetic layer end-to-end**, axiom-clean (only `propext`,
`Classical.choice`, `Quot.sound`):

Isosceles branch:
* `k_not_dvd_sum_sub`, `M_not_int` — the Φ-invariant tile count is never an integer.
* `iso_reduction_identity` — the algebraic identity behind the isosceles boundary reduction.
* `prime_count_forces_scale` — the area equation `N·b = k²(a + 2b)` with `N` prime and
  `gcd(a, b) = 1` forces `b = k²` and `N = a + 2b`.
* `no_prime_isosceles_count` — **master theorem**: the full isosceles arithmetic in one
  statement — no `(a, b, c, k, N)` with `N` prime satisfies the 120°-relation, the area
  equation, and the Φ-divisibility `(c + a − b) ∣ k(2b + a − 2c)` simultaneously.

Scalene branches (the tile counts of Laczkovich's four families are composite):
* `add_not_prime` — for a 120°-triple, `a + b` is never prime (over ℤ; coprimality not even
  needed — it holds for every positive `a, b, c` with `c² = a² + ab + b²`).
* `not_prime_of_two_le` — a product of two integer factors `≥ 2` is not prime.
* `F1_count_not_prime` … `F4_count_not_prime` — the four scalene tile counts `t(a + b)`,
  `(a + 2b)(2a + b)`, `3(a + b)(a + 2b)`, `(a + b)(2a + b)` are never prime.

Commensurable branch:
* `prime_three_mod_four_excluded` — a prime `≡ 3 (mod 4)` exceeding `3` is none of the
  commensurable-angle forms `{square, sum of two squares, 2·□, 3·□, 6·□}` (Beeson–Laczkovich),
  using Fermat's two-squares theorem from Mathlib (`Nat.eq_sq_add_sq_iff`).

Shape classification:
* `shape_enumeration` — the eleven-shape list: a corner type `(m, k) : ℤ × ℤ` is realizable iff
  `(1 ≤ k ∧ −k ≤ m) ∨ (k = 0 ∧ 1 ≤ m)`; the lexicographically sorted triples of realizable corner
  types with `m₁ + m₂ + m₃ = 0` and `k₁ + k₂ + k₃ = 3` are exactly the eleven shapes of the
  paper's case analysis.

The *geometric* ingredients of the paper (the Φ-invariant's cancellation and tile-value lemmas,
Laczkovich's case analysis, Beeson's equilateral input) are **not** formalized — there is no theory
of triangle dissections in Mathlib — and remain human-checked in the paper.
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

/-- A product of two integer factors each `≥ 2` is not prime. -/
theorem not_prime_of_two_le (u v : ℤ) (hu : 2 ≤ u) (hv : 2 ≤ v) : ¬ Prime (u * v) := by
  intro hp
  rcases hp.irreducible.isUnit_or_isUnit rfl with h | h <;>
    rw [Int.isUnit_iff] at h <;> omega

/-- **Scale-pinning.** If a prime `N` satisfies the area equation `N·b = k²(a + 2b)` with
`gcd(a, b) = 1`, then `b = k²` and `N = a + 2b`. -/
theorem prime_count_forces_scale (a b k N : ℤ) (ha : 0 < a) (hb : 0 < b) (hk : 0 < k)
    (hcop : IsCoprime a b) (hN : Prime N) (harea : N * b = k ^ 2 * (a + 2 * b)) :
    b = k ^ 2 ∧ N = a + 2 * b := by
  -- `a + 2b` is coprime to `b`
  have hcop2 : IsCoprime (a + 2 * b) b := hcop.add_mul_right_left 2
  -- `b ∣ k²(a + 2b)`, hence `b ∣ k²` by coprimality
  have hdvd : b ∣ k ^ 2 * (a + 2 * b) := ⟨N, by linear_combination -harea⟩
  have hbk2 : b ∣ k ^ 2 := hcop2.symm.dvd_of_dvd_mul_right hdvd
  obtain ⟨m, hm⟩ := hbk2
  have hmpos : 0 < m := by
    have h : 0 < b * m := by rw [← hm]; exact pow_pos hk 2
    exact (mul_pos_iff_of_pos_left hb).mp h
  -- cancel `b` in the area equation:  N = m(a + 2b)
  have hNm : N = m * (a + 2 * b) := by
    have h1 : b * N = b * (m * (a + 2 * b)) := by
      linear_combination harea + (a + 2 * b) * hm
    exact mul_left_cancel₀ (ne_of_gt hb) h1
  -- primality of `N` forces `m` to be the unit
  rcases hN.irreducible.isUnit_or_isUnit hNm with hu | hu
  · rw [Int.isUnit_iff] at hu
    have hm1 : m = 1 := by omega
    subst hm1
    exact ⟨by linear_combination -hm, by linear_combination hNm⟩
  · rw [Int.isUnit_iff] at hu
    omega

/-- **Master theorem (isosceles branch).** For a primitive 120°-triple `(a, b, c)` there is no
prime tile count `N` satisfying the area equation `N·b = k²(a + 2b)` together with the
Φ-invariant divisibility `(c + a − b) ∣ k(2b + a − 2c)`. -/
theorem no_prime_isosceles_count (a b c k N : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hk : 0 < k)
    (hcop : IsCoprime a b) (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hN : Prime N) (harea : N * b = k ^ 2 * (a + 2 * b))
    (hphi : (c + a - b) ∣ k * (2 * b + a - 2 * c)) : False := by
  -- the area equation pins the scale:  b = k²
  obtain ⟨hbk, -⟩ := prime_count_forces_scale a b k N ha hb hk hcop hN harea
  subst hbk
  have hc2' : c ^ 2 = a ^ 2 + a * k ^ 2 + k ^ 4 := by linear_combination hc2
  have hcopk : IsCoprime a k :=
    hcop.of_isCoprime_of_dvd_right (dvd_pow_self k (by norm_num))
  -- positivity of the cancelled factor:  c > k²
  have hck : k ^ 2 < c := by
    nlinarith [hc2', pow_pos hk 2, mul_pos ha (pow_pos hk 2), sq_nonneg a, hc]
  have hpos : 0 < c + a - k ^ 2 := by linarith
  obtain ⟨M, hM⟩ := hphi
  -- reduction identity + Φ-divisibility  ⇒  (c − a − k²) = kM  after cancelling (c + a − k²)
  have hkey : (c - a - k ^ 2) * (c + a - k ^ 2) = (k * M) * (c + a - k ^ 2) := by
    linear_combination iso_reduction_identity a k c ha hk hc2' + k * hM
  have hcancel : c - a - k ^ 2 = k * M := mul_right_cancel₀ (ne_of_gt hpos) hkey
  -- contradiction with the non-integrality of the Φ-invariant tile count
  exact M_not_int a k c ha hk hcopk hc2' hc ⟨M, by linear_combination hcancel⟩

/-- **Scalene family F1.** The tile count `t(a + b)`, `t ≥ 1`, is never prime for a
120°-triple. -/
theorem F1_count_not_prime (a b c t : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hcop : IsCoprime a b) (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) (ht : 1 ≤ t) :
    ¬ Prime (t * (a + b)) := by
  rcases ht.eq_or_lt with h | h
  · subst h
    simpa using add_not_prime a b c ha hb hcop hc2 hc
  · exact not_prime_of_two_le t (a + b) (by omega) (by omega)

/-- **Scalene family F2.** The tile count `(a + 2b)(2a + b)` is never prime. -/
theorem F2_count_not_prime (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    ¬ Prime ((a + 2 * b) * (2 * a + b)) :=
  not_prime_of_two_le _ _ (by omega) (by omega)

/-- **Scalene family F3.** The tile count `3(a + b)(a + 2b)` is never prime. -/
theorem F3_count_not_prime (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    ¬ Prime (3 * ((a + b) * (a + 2 * b))) := by
  have hfac : 2 ≤ (a + b) * (a + 2 * b) := by
    have h1 : 2 ≤ a + b := by omega
    have h2 : 3 ≤ a + 2 * b := by omega
    nlinarith
  exact not_prime_of_two_le 3 _ (by norm_num) hfac

/-- **Scalene family F4.** The tile count `(a + b)(2a + b)` is never prime. -/
theorem F4_count_not_prime (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    ¬ Prime ((a + b) * (2 * a + b)) :=
  not_prime_of_two_le _ _ (by omega) (by omega)

set_option maxHeartbeats 1000000 in
/-- **The eleven-shape enumeration.** A corner type `(m, k) : ℤ × ℤ` is *realizable* iff
`(1 ≤ k ∧ −k ≤ m) ∨ (k = 0 ∧ 1 ≤ m)`.  The lexicographically sorted triples of realizable
corner types with `m₁ + m₂ + m₃ = 0` and `k₁ + k₂ + k₃ = 3` are exactly the eleven shapes of
the paper's case analysis. -/
theorem shape_enumeration (m1 k1 m2 k2 m3 k3 : ℤ)
    (h1 : (1 ≤ k1 ∧ -k1 ≤ m1) ∨ (k1 = 0 ∧ 1 ≤ m1))
    (h2 : (1 ≤ k2 ∧ -k2 ≤ m2) ∨ (k2 = 0 ∧ 1 ≤ m2))
    (h3 : (1 ≤ k3 ∧ -k3 ≤ m3) ∨ (k3 = 0 ∧ 1 ≤ m3))
    (hsort12 : m1 < m2 ∨ (m1 = m2 ∧ k1 ≤ k2))
    (hsort23 : m2 < m3 ∨ (m2 = m3 ∧ k2 ≤ k3))
    (hm : m1 + m2 + m3 = 0) (hk : k1 + k2 + k3 = 3) :
    (m1 = -3 ∧ k1 = 3 ∧ m2 = 1 ∧ k2 = 0 ∧ m3 = 2 ∧ k3 = 0) ∨
    (m1 = -2 ∧ k1 = 2 ∧ m2 = -1 ∧ k2 = 1 ∧ m3 = 3 ∧ k3 = 0) ∨
    (m1 = -2 ∧ k1 = 2 ∧ m2 = 0 ∧ k2 = 1 ∧ m3 = 2 ∧ k3 = 0) ∨
    (m1 = -2 ∧ k1 = 2 ∧ m2 = 1 ∧ k2 = 0 ∧ m3 = 1 ∧ k3 = 1) ∨
    (m1 = -2 ∧ k1 = 3 ∧ m2 = 1 ∧ k2 = 0 ∧ m3 = 1 ∧ k3 = 0) ∨
    (m1 = -1 ∧ k1 = 1 ∧ m2 = -1 ∧ k2 = 1 ∧ m3 = 2 ∧ k3 = 1) ∨
    (m1 = -1 ∧ k1 = 1 ∧ m2 = -1 ∧ k2 = 2 ∧ m3 = 2 ∧ k3 = 0) ∨
    (m1 = -1 ∧ k1 = 1 ∧ m2 = 0 ∧ k2 = 1 ∧ m3 = 1 ∧ k3 = 1) ∨
    (m1 = -1 ∧ k1 = 1 ∧ m2 = 0 ∧ k2 = 2 ∧ m3 = 1 ∧ k3 = 0) ∨
    (m1 = -1 ∧ k1 = 2 ∧ m2 = 0 ∧ k2 = 1 ∧ m3 = 1 ∧ k3 = 0) ∨
    (m1 = 0 ∧ k1 = 1 ∧ m2 = 0 ∧ k2 = 1 ∧ m3 = 0 ∧ k3 = 1) := by
  -- Pin one variable at a time: every omega goal below is a disjunction of at most three
  -- single equalities, and the eleven-way goal is only ever closed by explicit Or-introduction.
  have hk1 : k1 = 1 ∨ k1 = 2 ∨ k1 = 3 := by omega
  rcases hk1 with rfl | rfl | rfl
  · -- k1 = 1
    have hk2 : k2 = 1 ∨ k2 = 2 := by omega
    rcases hk2 with rfl | rfl
    · -- (k1,k2,k3) = (1,1,1)
      have hk3 : k3 = 1 := by omega
      subst hk3
      have hm1 : m1 = -1 ∨ m1 = 0 := by omega
      rcases hm1 with rfl | rfl
      · have hm2 : m2 = -1 ∨ m2 = 0 := by omega
        rcases hm2 with rfl | rfl
        · have hm3 : m3 = 2 := by omega
          subst hm3
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)))))
        · have hm3 : m3 = 1 := by omega
          subst hm3
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)))))))
      · have hm2 : m2 = 0 := by omega
        subst hm2
        have hm3 : m3 = 0 := by omega
        subst hm3
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)))))))))
    · -- (k1,k2,k3) = (1,2,0)
      have hk3 : k3 = 0 := by omega
      subst hk3
      have hm1 : m1 = -1 := by omega
      subst hm1
      have hm2 : m2 = -1 ∨ m2 = 0 := by omega
      rcases hm2 with rfl | rfl
      · have hm3 : m3 = 2 := by omega
        subst hm3
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩))))))
      · have hm3 : m3 = 1 := by omega
        subst hm3
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩))))))))
  · -- k1 = 2
    have hk2 : k2 = 0 ∨ k2 = 1 := by omega
    rcases hk2 with rfl | rfl
    · -- (k1,k2,k3) = (2,0,1)
      have hk3 : k3 = 1 := by omega
      subst hk3
      have hm1 : m1 = -2 := by omega
      subst hm1
      have hm2 : m2 = 1 := by omega
      subst hm2
      have hm3 : m3 = 1 := by omega
      subst hm3
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)))
    · -- (k1,k2,k3) = (2,1,0)
      have hk3 : k3 = 0 := by omega
      subst hk3
      have hm1 : m1 = -2 ∨ m1 = -1 := by omega
      rcases hm1 with rfl | rfl
      · have hm2 : m2 = -1 ∨ m2 = 0 := by omega
        rcases hm2 with rfl | rfl
        · have hm3 : m3 = 3 := by omega
          subst hm3
          exact Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
        · have hm3 : m3 = 2 := by omega
          subst hm3
          exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩))
      · have hm2 : m2 = 0 := by omega
        subst hm2
        have hm3 : m3 = 1 := by omega
        subst hm3
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)))))))))
  · -- k1 = 3, so (k1,k2,k3) = (3,0,0)
    have hk2 : k2 = 0 := by omega
    subst hk2
    have hk3 : k3 = 0 := by omega
    subst hk3
    have hm1 : m1 = -3 ∨ m1 = -2 := by omega
    rcases hm1 with rfl | rfl
    · have hm2 : m2 = 1 := by omega
      subst hm2
      have hm3 : m3 = 2 := by omega
      subst hm3
      exact Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · have hm2 : m2 = 1 := by omega
      subst hm2
      have hm3 : m3 = 1 := by omega
      subst hm3
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩))))

/-- **Sum of two positive squares.** A prime `p ≢ 3 (mod 4)` is a sum of two *positive* squares
(Fermat).  This is the arithmetic content of the achievability half of the prime dichotomy: the
biquadratic tiling realizes `N = e² + f²` tiles for any `e, f ≥ 1`, so together with
`no_prime_isosceles_count` and its companions, a prime `p` is a number of congruent triangles
tiling a triangle iff `p = 2`, `p = 3`, or `p ≡ 1 (mod 4)`. -/
theorem prime_sum_two_pos_squares (p : ℕ) (hp : p.Prime) (h4 : p % 4 ≠ 3) :
    ∃ e f : ℕ, 1 ≤ e ∧ 1 ≤ f ∧ e ^ 2 + f ^ 2 = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨e, f, hef⟩ := Nat.Prime.sq_add_sq h4
  have hsq : ∀ r : ℕ, r ^ 2 ≠ p := by
    intro r hr
    have hrdvd : r ∣ p := ⟨r, by rw [← hr]; ring⟩
    rcases hp.eq_one_or_self_of_dvd r hrdvd with h | h
    · subst h
      have := hp.two_le
      simp at hr
      omega
    · subst h
      nlinarith [hp.two_le, hr]
  rcases Nat.eq_zero_or_pos e with rfl | he
  · exact absurd (by simpa using hef) (hsq f)
  rcases Nat.eq_zero_or_pos f with rfl | hf
  · exact absurd (by simpa using hef) (hsq e)
  exact ⟨e, f, he, hf, hef⟩

/-- **General-`N` admissibility for the isosceles branch.**  Write `b = d·e²` with `d` squarefree.
Any tile count `N` compatible with the area equation `N·b = k²(a+2b)` and the Φ-divisibility
`(c+a−b) ∣ k(2b+a−2c)` on the base-α isosceles target has the form `N = d·w²·(a+2b)` with scale
`k = d·e·w`, and moreover `e ∣ w(c−a−b)`.  For prime `N` this forces `d = w = 1`, so `b = e²` and
`e ∣ (c−a−b)`, which `k_not_dvd_sum_sub` refutes: `no_prime_isosceles_count` is the degenerate
case `d = w = 1` of this statement. -/
theorem iso_admissible (a b c k N d e : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hk : 0 < k) (hd : 0 < d) (he : 0 < e)
    (hsf : Squarefree d) (hbde : b = d * e ^ 2) (hcop : IsCoprime a b)
    (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (harea : N * b = k ^ 2 * (a + 2 * b))
    (hphi : (c + a - b) ∣ k * (2 * b + a - 2 * c)) :
    ∃ w : ℤ, k = d * e * w ∧ N = d * w ^ 2 * (a + 2 * b) ∧ e ∣ w * (c - a - b) := by
  subst hbde
  -- the area equation forces `b ∣ k²`
  have hcop2 : IsCoprime (a + 2 * (d * e ^ 2)) (d * e ^ 2) := hcop.add_mul_right_left 2
  have hbk2 : (d * e ^ 2) ∣ k ^ 2 :=
    hcop2.symm.dvd_of_dvd_mul_right ⟨N, by linear_combination -harea⟩
  -- hence `e ∣ k`
  have he2 : e ^ 2 ∣ k ^ 2 := dvd_trans ⟨d, by ring⟩ hbk2
  have hek : e ∣ k := (IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).mp he2
  obtain ⟨k₁, hk₁⟩ := hek
  subst hk₁
  -- and `d ∣ k₁` by squarefreeness
  have hd1 : d ∣ k₁ ^ 2 := by
    have h : e ^ 2 * d ∣ e ^ 2 * k₁ ^ 2 := by
      calc e ^ 2 * d = d * e ^ 2 := by ring
        _ ∣ (e * k₁) ^ 2 := hbk2
        _ = e ^ 2 * k₁ ^ 2 := by ring
    exact (mul_dvd_mul_iff_left (pow_ne_zero 2 (ne_of_gt he))).mp h
  have hdk1 : d ∣ k₁ := (hsf.dvd_pow_iff_dvd two_ne_zero).mp hd1
  obtain ⟨w, hw⟩ := hdk1
  subst hw
  refine ⟨w, by ring, ?_, ?_⟩
  · -- the count: `N = d w² (a+2b)`
    have hBne : (d * e ^ 2 : ℤ) ≠ 0 :=
      mul_ne_zero (ne_of_gt hd) (pow_ne_zero 2 (ne_of_gt he))
    have h : (d * e ^ 2) * N = (d * e ^ 2) * (d * w ^ 2 * (a + 2 * (d * e ^ 2))) := by
      linear_combination harea
    exact mul_left_cancel₀ hBne h
  · -- the Φ-divisibility descends to `e ∣ w(c−a−b)`
    have hpos : 0 < c + a - d * e ^ 2 := by
      nlinarith [hc2, mul_pos hd (pow_pos he 2), mul_pos ha (mul_pos hd (pow_pos he 2)), hc,
        sq_nonneg (c + a - d * e ^ 2), sq_nonneg (c - a + d * e ^ 2)]
    obtain ⟨M, hM⟩ := hphi
    have hid : (c - a - d * e ^ 2) * (c + a - d * e ^ 2)
        = (d * e ^ 2) * (2 * (d * e ^ 2) + a - 2 * c) := by
      linear_combination hc2
    have hzero : (c + a - d * e ^ 2)
        * (e * d * (w * (c - a - d * e ^ 2)) - e * d * (e * M)) = 0 := by
      linear_combination (e * d * w) * hid + (d * e ^ 2) * hM
    have hcancel : e * d * (w * (c - a - d * e ^ 2)) = e * d * (e * M) := by
      rcases mul_eq_zero.mp hzero with h | h
      · exact absurd h (ne_of_gt hpos)
      · linarith
    exact ⟨M, mul_left_cancel₀ (mul_ne_zero (ne_of_gt he) (ne_of_gt hd)) hcancel⟩

/-- **Frontier check (π/3-equilateral).** Beeson's square criterion — an equilateral triangle
`N`-tiled by a `(α, β, π/3)` tile forces `(9N − M²)(N − M²)` to be a perfect square for some
positive `M` with `M² < N` — fails for every admissible `M` at `N = 14` and `N = 15`. -/
theorem pi3_equilateral_fails_14_15 :
    (∀ M : ℕ, 0 < M → M ^ 2 < 14 → ¬ ∃ q, q * q = (9 * 14 - M ^ 2) * (14 - M ^ 2)) ∧
    (∀ M : ℕ, 0 < M → M ^ 2 < 15 → ¬ ∃ q, q * q = (9 * 15 - M ^ 2) * (15 - M ^ 2)) := by
  constructor
  all_goals
    intro M h1 h2
    have hM : M ≤ 3 := by nlinarith
    interval_cases M
    all_goals
      rintro ⟨q, hqq⟩
      have hqb : q ≤ 43 := by
        by_contra hc
        push_neg at hc
        have h44 : 44 ≤ q := hc
        have := Nat.mul_le_mul h44 h44
        omega
      interval_cases q <;> omega

/-- **Frontier check (`3α+2β=π`, shape with the first tiling equation).** The complete
characterization `N = 2K² − M²` with `K ∣ M²` (Beeson) has no admissible solution at
`N = 14` or `N = 15`. -/
theorem shapeA_fails_14_15 :
    (∀ M K : ℕ, 0 < M → 0 < K → M ^ 2 < 14 → 2 * K ^ 2 = 14 + M ^ 2 → ¬ (K ∣ M ^ 2)) ∧
    (∀ M K : ℕ, 0 < M → 0 < K → M ^ 2 < 15 → 2 * K ^ 2 = 15 + M ^ 2 → False) := by
  constructor <;> intro M K hM hK h1 h2
  · have hMb : M ≤ 3 := by nlinarith
    have hKb : K ≤ 3 := by nlinarith
    interval_cases M <;> interval_cases K <;> omega
  · have hMb : M ≤ 3 := by nlinarith
    have hKb : K ≤ 3 := by nlinarith
    interval_cases M <;> interval_cases K <;> omega

/-- **Frontier check (`2π/3`-equilateral, `N = 14`).** In the criterion of the paper
(`st = 3N`, `(t−s)² + 16N` a square), the only factor pair for `N = 14` is `(s,t) = (6,7)`:
the unique admissible instance is the tile `(7,8,13)` on the equilateral triangle of side 28. -/
theorem eq_spectrum_unique_14 :
    ∀ s t : ℕ, 0 < s → s * t = 42 → s ≤ t →
      (∃ q, q * q = (t - s) ^ 2 + 224) → s = 6 ∧ t = 7 := by
  intro s t hs hst hle hq
  have hsb : s ≤ 6 := by
    by_contra h
    push_neg at h
    have h7 : 7 ≤ s := h
    have := Nat.mul_le_mul h7 (le_trans h7 hle)
    omega
  have hpairs : (s = 1 ∧ t = 42) ∨ (s = 2 ∧ t = 21) ∨ (s = 3 ∧ t = 14) ∨
      (s = 6 ∧ t = 7) := by
    interval_cases s <;> omega
  obtain ⟨q, hqq⟩ := hq
  have hqb : q ≤ 45 := by
    by_contra hc
    push_neg at hc
    have h46 : 46 ≤ q := hc
    have := Nat.mul_le_mul h46 h46
    rcases hpairs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
  rcases hpairs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact absurd hqq (by interval_cases q <;> omega)
  · exact absurd hqq (by interval_cases q <;> omega)
  · exact absurd hqq (by interval_cases q <;> omega)
  · exact ⟨rfl, rfl⟩

/-- **Frontier check (`2π/3`-equilateral, `N = 15`).** For `N = 15` the only factor pair is
`(s,t) = (5,9)`: the unique admissible instance is the tile `(3,5,7)` on side 15. -/
theorem eq_spectrum_unique_15 :
    ∀ s t : ℕ, 0 < s → s * t = 45 → s ≤ t →
      (∃ q, q * q = (t - s) ^ 2 + 240) → s = 5 ∧ t = 9 := by
  intro s t hs hst hle hq
  have hsb : s ≤ 6 := by
    by_contra h
    push_neg at h
    have h7 : 7 ≤ s := h
    have := Nat.mul_le_mul h7 (le_trans h7 hle)
    omega
  have hpairs : (s = 1 ∧ t = 45) ∨ (s = 3 ∧ t = 15) ∨ (s = 5 ∧ t = 9) := by
    interval_cases s <;> omega
  obtain ⟨q, hqq⟩ := hq
  have hqb : q ≤ 47 := by
    by_contra hc
    push_neg at hc
    have h48 : 48 ≤ q := hc
    have := Nat.mul_le_mul h48 h48
    rcases hpairs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
  rcases hpairs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact absurd hqq (by interval_cases q <;> omega)
  · exact absurd hqq (by interval_cases q <;> omega)
  · exact ⟨rfl, rfl⟩

/-- **Frontier check (`3α+2β=π`, iso-`(α+β)`, `N = 14`).** The unique tiling-equation candidate,
tile `(45,56,81)` with `M = 2`, dies on Beeson's boundary congruence: `M ≡ −m (mod gcd(a,c))`
forces the base `140 = 45p + 56m + 81q` to carry `m ≡ 7 (mod 9)` edges of length 56 —
impossible. -/
theorem iso_ab_congruence_kills_14 :
    ¬ ∃ p m q : ℕ, 140 = 45 * p + 56 * m + 81 * q ∧ (2 + m) % 9 = 0 := by
  rintro ⟨p, m, q, h1, h2⟩
  omega

end Erdos634

#print axioms Erdos634.k_not_dvd_sum_sub
#print axioms Erdos634.M_not_int
#print axioms Erdos634.iso_reduction_identity
#print axioms Erdos634.add_not_prime
#print axioms Erdos634.prime_three_mod_four_excluded
#print axioms Erdos634.not_prime_of_two_le
#print axioms Erdos634.prime_count_forces_scale
#print axioms Erdos634.no_prime_isosceles_count
#print axioms Erdos634.F1_count_not_prime
#print axioms Erdos634.F2_count_not_prime
#print axioms Erdos634.F3_count_not_prime
#print axioms Erdos634.F4_count_not_prime
#print axioms Erdos634.shape_enumeration
#print axioms Erdos634.prime_sum_two_pos_squares
#print axioms Erdos634.iso_admissible
#print axioms Erdos634.pi3_equilateral_fails_14_15
#print axioms Erdos634.shapeA_fails_14_15
#print axioms Erdos634.eq_spectrum_unique_14
#print axioms Erdos634.eq_spectrum_unique_15
#print axioms Erdos634.iso_ab_congruence_kills_14
