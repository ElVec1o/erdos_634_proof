import Mathlib.Tactic

/-!
# Boundary walks of the base-`β` target (Erdős #634, the `3α+2β=π` branch)

For the primitive `3α+2β=π` tile `(a,b,c) = (ef, f²−e², f²)` (`1 ≤ e < f`, `gcd(e,f)=1`) the
base-`β` target at scale `m` is the isosceles triangle with equal sides `X = f³m` and base
`Y = em(3f²−e²)`, cut into `N = m²(3f²−e²)` copies.  **`N` is prime exactly when `m = 1`**, so the
prime question lives entirely at `m = 1`, the case treated here.

Each side of the target is partitioned into whole tile edges, so a *walk* along a side is a triple
`(P,Q,R)` of edge multiplicities with `P·a + Q·b + R·c = (side length)`.  The theorems below
classify **all** such walks.  The content is that both walks are governed by the *same* linear form
`⟨e, f, 1⟩` — the base sitting at level `2e`, the equal side at level `f`:

* `base_walk_param` — base walks are exactly `p·e + j·f + R = 2e` with `(P,Q,R) = (je+fp, e+fj, R)`;
* `side_walk_param` — side walks are exactly `p·e + q·f + R = f`  with `(P,Q,R) = (qe+fp, fq, R)`.

Because a level bounds its solutions, this makes the walk set *finite and explicit for every*
`(e,f)` — the input the `e ≥ 2` analysis needs (previously only `e = 1` was understood, via
`BaseBetaE1.base_composition_e1`).  In the **thin regime `f > 2e`** it collapses to a short list:

* `base_trichotomy` — the base is one of exactly **three** walks, `{b^e, c^{2e}}`, `{a^f, b^e, c^e}`
  and `{a^{2f}, b^e}`; in particular it carries **exactly `e` `b`-edges**;
* `side_dichotomy` — the equal side is `{a^e, b^f}`, or `{a^{fp}, c^{f−pe}}` for some `p ≥ 0`.

`base_trichotomy` generalizes `BaseBetaE1.base_composition_e1` (the case `e = 1`, and there only
under an extra "at least two `c`-edges" hypothesis) to **every** `e` with `f > 2e`: an infinite
family — `e=1, f≥3`; `e=2, f≥5`; `e=3, f≥7`; … — covering the primes `N = 47, 71, 107, 143, …`.

The geometric companion is the *γ-injection lemma* (paper): on any side, each `a`-edge tile and each
`b`-edge tile carries a `γ`-vertex at one endpoint (`a` joins `β` to `γ`, `b` joins `α` to `γ`,
while `c` joins `α` to `β`), no `γ` sits at a base corner (`BaseBetaE1.vertex_beta_corner`: one tile,
angle `β`) or at the apex (`BaseBetaE1.vertex_apex`: three tiles, all `α`), and every other node of a
side is a `π`-vertex carrying **at most one** `γ` (`BaseBetaE1.vertex_pi`).  Hence
`#a + #b ≤ #edges − 1`, i.e. `R ≥ 1`: *every side carries a `c`-edge*.  Combined with the two
theorems below this kills the walks `{a^{2f}, b^e}` and `{a^e, b^f}` outright, so for `f > 2e` at
`m = 1` the base is `{b^e, c^{2e}}` or `{a^f, b^e, c^e}` and **the equal sides carry no `b`-edge at
all** — see `base_trichotomy_cfree` and `side_no_b`.

All statements are subtraction-free: `B` denotes `f²−e²` via `hB : B + e² = f²`.  Axiom-clean.
-/

namespace Erdos634.BaseBetaWalks

/-- If `f ∣ x − y` over `ℤ` with `y < f` and `x, y : ℕ`, then `x = y + f·j` for some `j : ℕ`.
(The least-nonnegative-residue step: a nonnegative `x` congruent to `y` mod `f` is `≥ y`.) -/
theorem exists_of_dvd_sub (f x y : ℕ) (hy : y < f) (hd : (f : ℤ) ∣ (x : ℤ) - (y : ℤ)) :
    ∃ j : ℕ, x = y + f * j := by
  obtain ⟨k, hk⟩ := hd
  have hx0 : (0 : ℤ) ≤ (x : ℤ) := Int.natCast_nonneg x
  have hyf : (y : ℤ) < (f : ℤ) := by exact_mod_cast hy
  have hf0 : (0 : ℤ) ≤ (f : ℤ) := Int.natCast_nonneg f
  have hk0 : 0 ≤ k := by
    by_contra hneg
    push_neg at hneg
    have hk1 : k ≤ -1 := by omega
    have hmul : (f : ℤ) * k ≤ (f : ℤ) * (-1) := mul_le_mul_of_nonneg_left hk1 hf0
    rw [← hk] at hmul
    linarith
  lift k to ℕ using hk0 with j
  have hx : (x : ℤ) = ((y + f * j : ℕ) : ℤ) := by push_cast; linarith
  exact ⟨j, by exact_mod_cast hx⟩

section

variable (e f P Q R B : ℕ)

/-- **The base walk parametrization** (`m = 1`).  A base walk `P·a + Q·b + R·c = e(3f²−e²)` has
`Q = e + f·j` and `P = j·e + f·p` for a unique `j : ℕ`, `p : ℤ` obeying the level equation
`p·e + j·f + R = 2e`.  The level `2e` is what bounds the solution set.  Also returns the halved
equation `P·e + j·B + R·f = 2ef`, which carries the size information. -/
theorem base_walk_param (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f)
    (hB : B + e ^ 2 = f ^ 2)
    (h : P * (e * f) + Q * B + R * f ^ 2 = e * (2 * f ^ 2 + B)) :
    ∃ j : ℕ, ∃ p : ℤ, Q = e + f * j ∧ (P : ℤ) = j * e + f * p ∧ p * e + j * f + R = 2 * e ∧
      P * e + j * B + R * f = 2 * (e * f) := by
  have hf0 : 0 < f := by omega
  have hf0' : (0 : ℤ) < (f : ℤ) := by exact_mod_cast hf0
  have hzc : IsCoprime (f : ℤ) (e : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr hcop.symm
  have hBz : (B : ℤ) = (f : ℤ) ^ 2 - (e : ℤ) ^ 2 := by
    have hc : ((B : ℤ)) + (e : ℤ) ^ 2 = (f : ℤ) ^ 2 := by exact_mod_cast hB
    linarith
  have hz : (P : ℤ) * ((e : ℤ) * f) + (Q : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) + (R : ℤ) * (f : ℤ) ^ 2
      = (e : ℤ) * (2 * (f : ℤ) ^ 2 + ((f : ℤ) ^ 2 - (e : ℤ) ^ 2)) := by
    have h' : (P : ℤ) * ((e : ℤ) * f) + (Q : ℤ) * (B : ℤ) + (R : ℤ) * (f : ℤ) ^ 2
        = (e : ℤ) * (2 * (f : ℤ) ^ 2 + (B : ℤ)) := by exact_mod_cast h
    rw [hBz] at h'; exact h'
  -- (1) `f ∣ Q − e` : the `b`-count is pinned mod `f`
  have hQe : (f : ℤ) ∣ ((Q : ℤ) - e) := by
    refine (hzc.pow_right (n := 2)).dvd_of_dvd_mul_right ?_
    exact ⟨(Q : ℤ) * f - 3 * e * f + P * e + R * f, by linear_combination -hz⟩
  obtain ⟨j, hj⟩ := exists_of_dvd_sub f Q e hef hQe
  have hjz : (Q : ℤ) = (e : ℤ) + (f : ℤ) * (j : ℤ) := by exact_mod_cast hj
  -- (2) divide by `f`
  have hhz : (P : ℤ) * e + (j : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) + (R : ℤ) * f
      = 2 * ((e : ℤ) * f) := by
    refine mul_left_cancel₀ (ne_of_gt hf0') ?_
    rw [hjz] at hz; linear_combination hz
  -- (3) `f ∣ P − j·e`
  have hPj : (f : ℤ) ∣ ((P : ℤ) - (j : ℤ) * e) := by
    refine hzc.dvd_of_dvd_mul_right ?_
    exact ⟨2 * (e : ℤ) - (j : ℤ) * f - R, by linear_combination hhz⟩
  obtain ⟨p, hp⟩ := hPj
  have hPz : (P : ℤ) = (j : ℤ) * e + (f : ℤ) * p := by linarith
  refine ⟨j, p, hj, hPz, ?_, ?_⟩
  · -- (4) the level equation
    refine mul_left_cancel₀ (ne_of_gt hf0') ?_
    rw [hPz] at hhz; linear_combination hhz
  · -- (5) the halved equation, back in ℕ
    have : ((P * e + j * B + R * f : ℕ) : ℤ) = ((2 * (e * f) : ℕ) : ℤ) := by
      push_cast; rw [hBz]; linarith
    exact_mod_cast this

/-- **The equal-side walk parametrization** (`m = 1`).  A walk `P·a + Q·b + R·c = f³` along an equal
side has `Q = f·q` and `P = q·e + f·p`, with level equation `p·e + q·f + R = f`. -/
theorem side_walk_param (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f)
    (hB : B + e ^ 2 = f ^ 2) (h : P * (e * f) + Q * B + R * f ^ 2 = f ^ 3) :
    ∃ q : ℕ, ∃ p : ℤ, Q = f * q ∧ (P : ℤ) = q * e + f * p ∧ p * e + q * f + R = f ∧
      P * e + q * B + R * f = f ^ 2 := by
  have hf0 : 0 < f := by omega
  have hf0' : (0 : ℤ) < (f : ℤ) := by exact_mod_cast hf0
  have hzc : IsCoprime (f : ℤ) (e : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr hcop.symm
  have hBz : (B : ℤ) = (f : ℤ) ^ 2 - (e : ℤ) ^ 2 := by
    have hc : ((B : ℤ)) + (e : ℤ) ^ 2 = (f : ℤ) ^ 2 := by exact_mod_cast hB
    linarith
  have hz : (P : ℤ) * ((e : ℤ) * f) + (Q : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) + (R : ℤ) * (f : ℤ) ^ 2
      = (f : ℤ) ^ 3 := by
    have h' : (P : ℤ) * ((e : ℤ) * f) + (Q : ℤ) * (B : ℤ) + (R : ℤ) * (f : ℤ) ^ 2 = (f : ℤ) ^ 3 := by
      exact_mod_cast h
    rw [hBz] at h'; exact h'
  -- (1) `f ∣ Q` : an equal side carries a multiple of `f` many `b`-edges
  have hQd : (f : ℤ) ∣ (Q : ℤ) := by
    refine (hzc.pow_right (n := 2)).dvd_of_dvd_mul_right ?_
    exact ⟨(Q : ℤ) * f - (f : ℤ) ^ 2 + P * e + R * f, by linear_combination -hz⟩
  obtain ⟨q, hq⟩ := exists_of_dvd_sub f Q 0 hf0 (by simpa using hQd)
  rw [Nat.zero_add] at hq
  have hqz : (Q : ℤ) = (f : ℤ) * (q : ℤ) := by exact_mod_cast hq
  -- (2) divide by `f`
  have hhz : (P : ℤ) * e + (q : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) + (R : ℤ) * f = (f : ℤ) ^ 2 := by
    refine mul_left_cancel₀ (ne_of_gt hf0') ?_
    rw [hqz] at hz; linear_combination hz
  -- (3) `f ∣ P − q·e`
  have hPq : (f : ℤ) ∣ ((P : ℤ) - (q : ℤ) * e) := by
    refine hzc.dvd_of_dvd_mul_right ?_
    exact ⟨(f : ℤ) - (q : ℤ) * f - R, by linear_combination hhz⟩
  obtain ⟨p, hp⟩ := hPq
  have hPz : (P : ℤ) = (q : ℤ) * e + (f : ℤ) * p := by linarith
  refine ⟨q, p, hq, hPz, ?_, ?_⟩
  · refine mul_left_cancel₀ (ne_of_gt hf0') ?_
    rw [hPz] at hhz; linear_combination hhz
  · have : ((P * e + q * B + R * f : ℕ) : ℤ) = ((f ^ 2 : ℕ) : ℤ) := by
      push_cast; rw [hBz]; linarith
    exact_mod_cast this

/-- **The base trichotomy** (`m = 1`, thin regime `f > 2e`).  The base of the base-`β` target admits
exactly three walks: `{b^e, c^{2e}}`, `{a^f, b^e, c^e}` and `{a^{2f}, b^e}`.  In every case it
carries **exactly `e` `b`-edges**.  Generalizes `BaseBetaE1.base_composition_e1` from `e = 1` to all
`e` with `f > 2e`. -/
theorem base_trichotomy (he : 1 ≤ e) (h2e : 2 * e < f) (hcop : Nat.Coprime e f)
    (hB : B + e ^ 2 = f ^ 2)
    (h : P * (e * f) + Q * B + R * f ^ 2 = e * (2 * f ^ 2 + B)) :
    (P = 0 ∧ Q = e ∧ R = 2 * e) ∨ (P = f ∧ Q = e ∧ R = e) ∨ (P = 2 * f ∧ Q = e ∧ R = 0) := by
  have hef : e < f := by omega
  have hf0 : 0 < f := by omega
  have hf0' : (0 : ℤ) < (f : ℤ) := by exact_mod_cast hf0
  obtain ⟨j, p, hQ, hP, hlev, hhalf⟩ := base_walk_param e f P Q R B he hef hcop hB h
  have hBz : (B : ℤ) + (e : ℤ) ^ 2 = (f : ℤ) ^ 2 := by exact_mod_cast hB
  have h2ez : 2 * (e : ℤ) < (f : ℤ) := by exact_mod_cast h2e
  have hez : (1 : ℤ) ≤ (e : ℤ) := by exact_mod_cast he
  -- (a) `j ≤ 1` : two copies of `B` already exceed `2ef` once `f > 2e`
  have hj1 : j ≤ 1 := by
    by_contra hc
    push_neg at hc
    have h2B : 2 * B ≤ j * B := Nat.mul_le_mul_right _ (by omega)
    have hBef : B ≤ e * f := by omega
    have hBefz : (B : ℤ) ≤ (e : ℤ) * (f : ℤ) := by exact_mod_cast hBef
    nlinarith [hBz, hBefz, h2ez, hez,
      mul_pos (show (0 : ℤ) < (f : ℤ) - 2 * e by linarith) (show (0 : ℤ) < (f : ℤ) + e by linarith)]
  -- (b) `j = 0` : `j = 1` forces `P ≥ e` (as `P ≡ e` mod `f`), hence `f² ≤ 2ef`, i.e. `f ≤ 2e`
  have hj0 : j = 0 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj1 with h0 | h1
    · exact h0
    · exfalso
      subst h1
      have hPd : (f : ℤ) ∣ ((P : ℤ) - e) := ⟨p, by push_cast at hP ⊢; linarith⟩
      obtain ⟨t, ht⟩ := exists_of_dvd_sub f P e hef hPd
      have hPe : e ≤ P := by omega
      have hmul : e * e ≤ P * e := Nat.mul_le_mul_right _ hPe
      have hsmall : e * e + B ≤ 2 * (e * f) := by omega
      have hsz : (e : ℤ) * (e : ℤ) + (B : ℤ) ≤ 2 * ((e : ℤ) * (f : ℤ)) := by exact_mod_cast hsmall
      nlinarith [hBz, hsz, h2ez, hez,
        mul_pos (show (0 : ℤ) < (f : ℤ) - 2 * e by linarith) (show (0 : ℤ) < (f : ℤ) by linarith)]
  subst hj0
  -- (c) `j = 0` : `P = f·u` with `u ∈ {0,1,2}` and `R = e(2−u)`
  have hp0 : 0 ≤ p := by
    by_contra hc
    push_neg at hc
    have hpm : p ≤ -1 := by omega
    have hmul : (f : ℤ) * p ≤ (f : ℤ) * (-1) := mul_le_mul_of_nonneg_left hpm (le_of_lt hf0')
    have hPn : (0 : ℤ) ≤ (P : ℤ) := Int.natCast_nonneg P
    push_cast at hP
    linarith
  lift p to ℕ using hp0 with u
  have hQe : Q = e := by omega
  have hPu : P = f * u := by
    have hc : (P : ℤ) = ((f * u : ℕ) : ℤ) := by push_cast at hP ⊢; linarith
    exact_mod_cast hc
  have hlevN : u * e + R = 2 * e := by
    have hc : ((u * e + R : ℕ) : ℤ) = ((2 * e : ℕ) : ℤ) := by push_cast at hlev ⊢; linarith
    exact_mod_cast hc
  have hu2 : u ≤ 2 := by
    by_contra hc
    push_neg at hc
    have : 3 * e ≤ u * e := Nat.mul_le_mul_right _ (by omega)
    omega
  interval_cases u
  · exact Or.inl ⟨by omega, hQe, by omega⟩
  · exact Or.inr (Or.inl ⟨by omega, hQe, by omega⟩)
  · exact Or.inr (Or.inr ⟨by omega, hQe, by omega⟩)

/-- **The equal-side dichotomy** (`m = 1`, thin regime `f > 2e`).  The equal side `X = f³` admits
exactly the walks `{a^e, b^f}` and `{a^{fu}, c^{f−ue}}` (`u ≥ 0`).  In particular a walk carrying any
`b`-edge carries exactly `f` of them and **no** `c`-edge. -/
theorem side_dichotomy (he : 1 ≤ e) (h2e : 2 * e < f) (hcop : Nat.Coprime e f)
    (hB : B + e ^ 2 = f ^ 2) (h : P * (e * f) + Q * B + R * f ^ 2 = f ^ 3) :
    (P = e ∧ Q = f ∧ R = 0) ∨ (∃ u : ℕ, Q = 0 ∧ P = f * u ∧ u * e + R = f) := by
  have hef : e < f := by omega
  have hf0 : 0 < f := by omega
  have hf0' : (0 : ℤ) < (f : ℤ) := by exact_mod_cast hf0
  obtain ⟨q, p, hQ, hP, hlev, hhalf⟩ := side_walk_param e f P Q R B he hef hcop hB h
  have hBz : (B : ℤ) + (e : ℤ) ^ 2 = (f : ℤ) ^ 2 := by exact_mod_cast hB
  have h2ez : 2 * (e : ℤ) < (f : ℤ) := by exact_mod_cast h2e
  have hez : (1 : ℤ) ≤ (e : ℤ) := by exact_mod_cast he
  -- (a) `q ≤ 1`
  have hq1 : q ≤ 1 := by
    by_contra hc
    push_neg at hc
    have h2B : 2 * B ≤ q * B := Nat.mul_le_mul_right _ (by omega)
    have hBf : 2 * B ≤ f ^ 2 := by omega
    have hBfz : 2 * (B : ℤ) ≤ (f : ℤ) ^ 2 := by exact_mod_cast hBf
    nlinarith [hBz, hBfz, h2ez, hez]
  interval_cases q
  · -- `q = 0` : `P = f·u`, `u·e + R = f`
    right
    have hp0 : 0 ≤ p := by
      by_contra hc
      push_neg at hc
      have hpm : p ≤ -1 := by omega
      have hmul : (f : ℤ) * p ≤ (f : ℤ) * (-1) := mul_le_mul_of_nonneg_left hpm (le_of_lt hf0')
      have hPn : (0 : ℤ) ≤ (P : ℤ) := Int.natCast_nonneg P
      push_cast at hP
      linarith
    lift p to ℕ using hp0 with u
    refine ⟨u, by omega, ?_, ?_⟩
    · have hc : (P : ℤ) = ((f * u : ℕ) : ℤ) := by push_cast at hP ⊢; linarith
      exact_mod_cast hc
    · have hc : ((u * e + R : ℕ) : ℤ) = ((f : ℕ) : ℤ) := by push_cast at hlev ⊢; linarith
      exact_mod_cast hc
  · -- `q = 1` : `P ≡ e` mod `f`, and `P·e + R·f = e²` pins `P = e`, `R = 0`
    left
    have hPd : (f : ℤ) ∣ ((P : ℤ) - e) := ⟨p, by push_cast at hP ⊢; linarith⟩
    obtain ⟨t, ht⟩ := exists_of_dvd_sub f P e hef hPd
    have hkey : P * e + R * f = e ^ 2 := by
      have hc : ((P * e + R * f : ℕ) : ℤ) = ((e ^ 2 : ℕ) : ℤ) := by
        push_cast
        have hc2 : ((P * e + 1 * B + R * f : ℕ) : ℤ) = ((f ^ 2 : ℕ) : ℤ) := by exact_mod_cast hhalf
        push_cast at hc2
        linarith
      exact_mod_cast hc
    have ht0 : t = 0 := by
      by_contra hc
      have h1t : 1 ≤ t := by omega
      have : e * f ≤ (f * t) * e := by
        calc e * f = f * 1 * e := by ring
        _ ≤ f * t * e := by
            exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1t)
      have hexp : P * e = e * e + f * t * e := by rw [ht]; ring
      nlinarith [hkey, hexp, this, hef, he]
    subst ht0
    simp only [Nat.mul_zero, Nat.add_zero] at ht
    subst ht
    refine ⟨rfl, by omega, ?_⟩
    nlinarith [hkey, hf0]

end

/-- **`c`-free walks are impossible** (γ-injection, paper).  Feeding `R ≥ 1` — *every side carries a
`c`-edge* — into the trichotomy kills `{a^{2f}, b^e}`: at `m = 1` with `f > 2e` the base is
`{b^e, c^{2e}}` or `{a^f, b^e, c^e}`. -/
theorem base_trichotomy_cfree (e f P Q R B : ℕ) (he : 1 ≤ e) (h2e : 2 * e < f)
    (hcop : Nat.Coprime e f) (hB : B + e ^ 2 = f ^ 2) (hR : 1 ≤ R)
    (h : P * (e * f) + Q * B + R * f ^ 2 = e * (2 * f ^ 2 + B)) :
    (P = 0 ∧ Q = e ∧ R = 2 * e) ∨ (P = f ∧ Q = e ∧ R = e) := by
  rcases base_trichotomy e f P Q R B he h2e hcop hB h with h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1
  · omega

/-- **The equal sides carry no `b`-edge** (γ-injection, paper).  Feeding `R ≥ 1` into the dichotomy
kills `{a^e, b^f}`: at `m = 1` with `f > 2e` every equal side is `{a^{fu}, c^{f−ue}}`.  This is the
`q_equal = 0` conclusion of the `e = 1` structure theorem, now for all `e` with `f > 2e`. -/
theorem side_no_b (e f P Q R B : ℕ) (he : 1 ≤ e) (h2e : 2 * e < f) (hcop : Nat.Coprime e f)
    (hB : B + e ^ 2 = f ^ 2) (hR : 1 ≤ R) (h : P * (e * f) + Q * B + R * f ^ 2 = f ^ 3) :
    Q = 0 ∧ ∃ u : ℕ, P = f * u ∧ u * e + R = f := by
  rcases side_dichotomy e f P Q R B he h2e hcop hB h with h1 | ⟨u, h1, h2, h3⟩
  · omega
  · exact ⟨h1, u, h2, h3⟩

end Erdos634.BaseBetaWalks

#print axioms Erdos634.BaseBetaWalks.exists_of_dvd_sub
#print axioms Erdos634.BaseBetaWalks.base_walk_param
#print axioms Erdos634.BaseBetaWalks.side_walk_param
#print axioms Erdos634.BaseBetaWalks.base_trichotomy
#print axioms Erdos634.BaseBetaWalks.side_dichotomy
#print axioms Erdos634.BaseBetaWalks.base_trichotomy_cfree
#print axioms Erdos634.BaseBetaWalks.side_no_b
