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

/-- **The equal sides carry no `b`-edge — for EVERY `(e,f)`** (γ-injection, paper).  No thinness
hypothesis: if a side carried `q ≥ 1` blocks of `b`-edges then `P = qe+fp ≥ 0` forces `fp ≥ -qe > -qf`
(as `e < f`), hence `p ≥ 1-q`, hence `R = f - pe - qf ≤ (1-q)(f-e) ≤ 0` — contradicting the γ-trap
`R ≥ 1`.  So at `m = 1` every equal side is `{a^{fu}, c^{f−ue}}`, and *all* boundary `b`-edges lie on
the base.  This is the `q_equal = 0` conclusion of the `e = 1` structure theorem, now for all `e`. -/
theorem side_no_b (e f P Q R B : ℕ) (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f)
    (hB : B + e ^ 2 = f ^ 2) (hR : 1 ≤ R) (h : P * (e * f) + Q * B + R * f ^ 2 = f ^ 3) :
    Q = 0 ∧ ∃ u : ℕ, P = f * u ∧ u * e + R = f := by
  have hf0 : 0 < f := by omega
  have hf0' : (0 : ℤ) < (f : ℤ) := by exact_mod_cast hf0
  have hez : (1 : ℤ) ≤ (e : ℤ) := by exact_mod_cast he
  have hefz : (e : ℤ) < (f : ℤ) := by exact_mod_cast hef
  have hRz : (1 : ℤ) ≤ (R : ℤ) := by exact_mod_cast hR
  obtain ⟨q, p, hQ, hP, hlev, hhalf⟩ := side_walk_param e f P Q R B he hef hcop hB h
  have hq0 : q = 0 := by
    by_contra hc
    have hq1z : (1 : ℤ) ≤ (q : ℤ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hc
    have hPn : (0 : ℤ) ≤ (P : ℤ) := Int.natCast_nonneg P
    -- `f*p > f*(-q)` : from `0 ≤ q*e + f*p` and `q*e < q*f`
    have hqef : (q : ℤ) * e < (q : ℤ) * f := by
      exact mul_lt_mul_of_pos_left hefz (by linarith)
    have hstep : (f : ℤ) * (-(q : ℤ)) < (f : ℤ) * p := by nlinarith [hPn, hP, hqef]
    have hp : -(q : ℤ) < p := lt_of_mul_lt_mul_left hstep (le_of_lt hf0')
    have hp1 : (1 : ℤ) - (q : ℤ) ≤ p := by omega
    -- `R ≤ (1-q)*(f-e) ≤ 0`
    have hpe : ((1 : ℤ) - (q : ℤ)) * e ≤ p * e := by
      exact mul_le_mul_of_nonneg_right hp1 (by linarith)
    have hprod : (0 : ℤ) ≤ ((q : ℤ) - 1) * ((f : ℤ) - e) := by
      exact mul_nonneg (by linarith) (by linarith)
    linarith [hlev, hpe, hprod, hRz]
  subst hq0
  have hp0 : 0 ≤ p := by
    by_contra hc
    push_neg at hc
    have hpm : p ≤ -1 := by omega
    have hmul : (f : ℤ) * p ≤ (f : ℤ) * (-1) := mul_le_mul_of_nonneg_left hpm (le_of_lt hf0')
    have hPn : (0 : ℤ) ≤ (P : ℤ) := Int.natCast_nonneg P
    push_cast at hP
    linarith
  lift p to ℕ using hp0 with u
  refine ⟨by omega, u, ?_, ?_⟩
  · have hc : (P : ℤ) = ((f * u : ℕ) : ℤ) := by push_cast at hP ⊢; linarith
    exact_mod_cast hc
  · have hc : ((u * e + R : ℕ) : ℤ) = ((f : ℕ) : ℤ) := by push_cast at hlev ⊢; linarith
    exact_mod_cast hc

/-- **The base's `b`-count is bounded — for EVERY `(e,f)`** (γ-injection, paper).  Writing the base's
`b`-count as `Q = e + f·j` (`base_walk_param`), the γ-trap `R ≥ 1` forces `j·(f−e) ≤ e−1`, stated
subtraction-free as `j·f + 1 ≤ j·e + e`.  Two consequences, both uniform in `f`:

* `e = 1` ⟹ `j·(f−1) ≤ 0` ⟹ `j = 0`: **the base carries exactly one `b`-edge**, for every `f`;
* `f > 2e` ⟹ `j·e < j·(f−e) ≤ e−1` ⟹ `j = 0`: the trichotomy of `base_trichotomy`.

The bound degrades exactly as `f` approaches `2e` — which is why the thick regime `f ≤ 2e` is where
the difficulty concentrates. -/
theorem base_b_bound (e f P Q R B j : ℕ) (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f)
    (hB : B + e ^ 2 = f ^ 2) (hR : 1 ≤ R) (hQ : Q = e + f * j)
    (h : P * (e * f) + Q * B + R * f ^ 2 = e * (2 * f ^ 2 + B)) :
    j * f + 1 ≤ j * e + e := by
  have hf0 : 0 < f := by omega
  have hf0' : (0 : ℤ) < (f : ℤ) := by exact_mod_cast hf0
  have hez : (1 : ℤ) ≤ (e : ℤ) := by exact_mod_cast he
  have hefz : (e : ℤ) < (f : ℤ) := by exact_mod_cast hef
  have hRz : (1 : ℤ) ≤ (R : ℤ) := by exact_mod_cast hR
  obtain ⟨j', p, hQ', hP, hlev, hhalf⟩ := base_walk_param e f P Q R B he hef hcop hB h
  -- `j` is determined by `Q`
  have hjj : j' = j := by
    have : f * j' = f * j := by omega
    exact Nat.eq_of_mul_eq_mul_left hf0 this
  subst hjj
  rcases Nat.eq_zero_or_pos j' with hz | hpos
  · subst hz; simpa using hez
  · have hjz : (1 : ℤ) ≤ (j' : ℤ) := by exact_mod_cast hpos
    have hPn : (0 : ℤ) ≤ (P : ℤ) := Int.natCast_nonneg P
    have hqef : (j' : ℤ) * e < (j' : ℤ) * f := mul_lt_mul_of_pos_left hefz (by linarith)
    have hstep : (f : ℤ) * (-(j' : ℤ)) < (f : ℤ) * p := by nlinarith [hPn, hP, hqef]
    have hp : -(j' : ℤ) < p := lt_of_mul_lt_mul_left hstep (le_of_lt hf0')
    have hp1 : (1 : ℤ) - (j' : ℤ) ≤ p := by omega
    have hpe : ((1 : ℤ) - (j' : ℤ)) * e ≤ p * e := mul_le_mul_of_nonneg_right hp1 (by linarith)
    -- `1 ≤ R = 2e - p·e - j·f ≤ e - j(f-e)`
    have hgoal : ((j' * f + 1 : ℕ) : ℤ) ≤ ((j' * e + e : ℕ) : ℤ) := by
      push_cast; linarith [hlev, hpe, hRz]
    exact_mod_cast hgoal

/-- **The γ-injection pigeonhole** — the combinatorial skeleton of the γ-trap, machine-checked.
`AB` is the set of `a`- and `b`-edges of one side of the target, `J` its set of interior junctions,
and `φ` assigns to each such edge a junction at which its tile places a `γ`-vertex.  The geometric
inputs are the two hypotheses: `hmap` (each `a`- or `b`-edge tile has its `γ` at an interior junction of
the side — true because `a` joins `β` to `γ` and `b` joins `α` to `γ`, while no `γ` fits at a base
corner or the apex, by `BaseBetaE1.vertex_beta_corner`/`vertex_apex`) and `hinj` (junctions host at
most one `γ`, by `BaseBetaE1.vertex_pi`: a `π`-vertex has type `3α+2β` or `α+β+γ`).  Conclusion:
there are at most `|J|` such edges. -/
theorem gamma_injection {ι κ : Type*} [DecidableEq κ] (AB : Finset ι) (J : Finset κ)
    (φ : ι → κ) (hmap : ∀ e ∈ AB, φ e ∈ J) (hinj : Set.InjOn φ AB) :
    AB.card ≤ J.card :=
  Finset.card_le_card_of_injOn φ hmap hinj

/-- **The γ-trap** in walk form: a side cut into `k = P + Q + R` whole edges has `k − 1` interior
junctions, so `gamma_injection` gives `P + Q ≤ k − 1`, i.e. `R ≥ 1` — every side of the target
carries a `c`-edge.  This is the hypothesis `hR` consumed by `side_no_b` and `base_b_bound`;
with this lemma its combinatorial content is machine-checked and only the vertex-figure facts
remain geometric. -/
theorem c_edge_exists (P Q R : ℕ) (hk : 1 ≤ P + Q + R)
    (hinj : P + Q ≤ (P + Q + R) - 1) : 1 ≤ R := by omega

/-- **The apex-mismatch core: the `e²` leftover is never exactly coverable.**  At `m = 1` (indeed
whenever both equal sides end with a `c`-edge) the three apex tiles are `α`-vertices; the outer two
carry `c` on the boundary and `b` inward, the middle one carries `b` and `c` inward.  So exactly one
inner apex ray carries the middle tile's `c` against a neighbour's `b`: a T-junction at distance `b`,
leaving a segment of length `c − b = e²` of the middle tile's `c`-edge.  This lemma shows the leftover
can never be exactly covered by whole tile edges — `n_a·ef + n_b·(f²−e²) + n_c·f² = e²` has **no**
solution — so some far-side edge must cross the middle tile's far `β`-corner: **every such tiling
contains a pierced `β`-corner at distance `f²` along an apex ray**.  (Killing `n_a, n_c` uses
`ef, f² > e²`; then `n_b·B = e²` gives `n_b·f² = (n_b+1)·e²`, coprimality forces `f² ∣ n_b + 1`,
hence `n_b ≥ f² − 1`, hence `e² = n_b·B ≥ f² − 1 ≥ e²` with equality forcing `B = 1` —
impossible since `B = f² − e² ≥ 2e + 1 ≥ 3`.)  Verified positionally on the genuine 44-tiling:
`V = (10, 2√15)` is pierced by a straight `b`-edge, sector `β + {α + γ}`. -/
theorem apex_leftover_nonrepresentable (e f na nb nc B : ℕ) (he : 1 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hB : B + e ^ 2 = f ^ 2) :
    na * (e * f) + nb * B + nc * f ^ 2 ≠ e ^ 2 := by
  intro h
  have hef2 : e ^ 2 < f ^ 2 := by nlinarith [hef, he]
  have hB1 : 1 ≤ B := by omega
  -- kill n_a : e·f > e²
  have hna : na = 0 := by
    by_contra hc
    have h1 : 1 ≤ na := Nat.one_le_iff_ne_zero.mpr hc
    have : e * f ≤ na * (e * f) := Nat.le_mul_of_pos_left _ (by omega)
    nlinarith [hef, he]
  -- kill n_c : f² > e²
  have hnc : nc = 0 := by
    by_contra hc
    have h1 : 1 ≤ nc := Nat.one_le_iff_ne_zero.mpr hc
    have : f ^ 2 ≤ nc * f ^ 2 := Nat.le_mul_of_pos_left _ (by omega)
    omega
  subst hna; subst hnc
  simp only [Nat.zero_mul, Nat.zero_add, Nat.add_zero] at h
  -- n_b·B = e², so n_b·f² = (n_b+1)·e²
  have hkey : nb * f ^ 2 = (nb + 1) * e ^ 2 := by
    have h2 : nb * f ^ 2 = nb * B + nb * e ^ 2 := by rw [← Nat.mul_add, hB]
    have h3 : (nb + 1) * e ^ 2 = nb * e ^ 2 + e ^ 2 := by ring
    omega
  -- coprimality: f² ∣ n_b + 1
  have hcop2 : Nat.Coprime (f ^ 2) (e ^ 2) := (hcop.symm.pow (n := 2) (m := 2))
  have hdvd : f ^ 2 ∣ (nb + 1) := by
    have h1 : f ^ 2 ∣ (nb + 1) * e ^ 2 := ⟨nb, by rw [← hkey]; ring⟩
    exact (Nat.Coprime.dvd_of_dvd_mul_right hcop2) h1
  have hge : f ^ 2 ≤ nb + 1 := Nat.le_of_dvd (by omega) hdvd
  -- e² = n_b·B ≥ n_b ≥ f²−1 ≥ e², equality forces B = 1: impossible since B ≥ 2e+1 ≥ 3
  have hBe : 2 * e + 1 ≤ B := by nlinarith [hef, he]
  have hnb : nb * 1 ≤ nb * B := Nat.mul_le_mul_left _ hB1
  omega

/-- **The pierced-corner vertex figure.**  On the middle tile's side of the piercing line the angles
fill `π − β`; writing the figure as `x·α + y·β + z·γ` and using `β = (π−3α)/2`, `γ = (π+α)/2`,
irrationality of `α/π` forces `y + z = 1` and `2x + z = 3y + 3`, whose only solutions are
`{3α, β}` and `{α, γ}` — the two continuation types of the pierced corner.  (The genuine 44-tiling
realizes `{α, γ}`.) -/
theorem pierced_corner_types (x y z : ℕ) (h1 : y + z = 1) (h2 : 2 * x + z = 3 * y + 3) :
    (x = 3 ∧ y = 1 ∧ z = 0) ∨ (x = 1 ∧ y = 0 ∧ z = 1) := by omega

/-- **Rung 2 of the pierced-corner chase: the pre-piercer edges are `b`'s, and only in the
super-thick regime.**  On the mismatch ray every full far-side edge strictly before the piercer lies
inside `[b, f²]`, so its length is at most `e²`.  Among the tile edges `{ef, f²−e², f²}` only
`b = f²−e²` can be `≤ e²`, and that requires `f² ≤ 2e²` (the *super-thick* regime, e.g.
`(e,f) = (4,5)`, `N = 59`).  Consequently the piercer starts at `(t+1)·b` with `t·b < e²`, and
`t = 0` outside super-thick; moreover at the first T-junction the `(1,1,1)` figure offers only
`{α, β}` corners while a `b`-piercer demands `{α, γ}` — so a `b`-piercer's corner there is exactly
`α`.  (All three claims verified positionally on the genuine 44-tiling: `t = 0`, piercer spans
`[3,6]`, corner `α` to numerical precision.) -/
theorem pre_pierce_dichotomy (e f ℓ B : ℕ) (he : 1 ≤ e) (hef : e < f)
    (hB : B + e ^ 2 = f ^ 2) (hmem : ℓ = e * f ∨ ℓ = B ∨ ℓ = f ^ 2) (hle : ℓ ≤ e ^ 2) :
    ℓ = B ∧ f ^ 2 ≤ 2 * e ^ 2 := by
  rcases hmem with h | h | h
  · exfalso; subst h; nlinarith [hef, he]
  · subst h; constructor
    · rfl
    · omega
  · exfalso; subst h; nlinarith [hef, he]

/-- **Unsplittability of `a` and `b`** — for *every* coprime `1 ≤ e < f`, with no size assumption.
Neither tile edge is a sum of two or more tile edges.  The proof is two mod-`f` reductions, and it must
avoid comparing `a = ef` with `b = f²−e²`: which is larger flips at the golden ratio (`b > a ⟺ f > φe`),
and the open *thick* regime is precisely where `b < a`.
For `= a`: mod `f` gives `f ∣ n_b·e²`, so `f ∣ n_b`; `n_b ≥ f` overshoots (`f·B > e·f` since `B > e`),
so `n_b = 0`, and cancelling `f` leaves `n_a·e + n_c·f = e`, forcing `n_c = 0`, `n_a = 1`.
For `= b`: mod `f` gives `f ∣ (n_b−1)·e²`, so `n_b ≡ 1`; `n_b ≥ 1+f` overshoots, so `n_b = 1` and the
rest vanishes, giving `n_a = n_c = 0`.  Either way the total is `1`, never `≥ 2`.
This is the exact hypothesis the corner-parallelogram rule needs, so that rule stands with **no
proviso**; and since the whole open thick regime has `e ≥ 2`, where `c` is unsplittable too
(`c = a^f` needs `e = 1`), **no tile edge splits at all there**. -/
theorem edge_ab_unsplittable (e f na nb nc B : ℕ) (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f)
    (hB : B + e ^ 2 = f ^ 2) (hn : 2 ≤ na + nb + nc) :
    na * (e * f) + nb * B + nc * f ^ 2 ≠ e * f ∧ na * (e * f) + nb * B + nc * f ^ 2 ≠ B := by
  have hf0 : 0 < f := by omega
  have hf1 : 1 < f := by omega
  have hef0 : 0 < e * f := by positivity
  have hBe : e < B := by nlinarith [hef, he]
  have hzc : IsCoprime (f : ℤ) (e : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr hcop.symm
  have hBz : (B : ℤ) = (f : ℤ) ^ 2 - (e : ℤ) ^ 2 := by
    have hc : ((B : ℤ)) + (e : ℤ) ^ 2 = (f : ℤ) ^ 2 := by exact_mod_cast hB
    linarith
  constructor
  · -- `= a` : mod `f` gives `f ∣ n_b`; `n_b ≥ f` overshoots; `n_b = 0` leaves `n_a·e + n_c·f = e`
    intro h
    have hz : (na : ℤ) * ((e : ℤ) * f) + (nb : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2)
        + (nc : ℤ) * (f : ℤ) ^ 2 = (e : ℤ) * f := by
      have h' : (na : ℤ) * ((e : ℤ) * f) + (nb : ℤ) * (B : ℤ) + (nc : ℤ) * (f : ℤ) ^ 2
          = (e : ℤ) * f := by exact_mod_cast h
      rw [hBz] at h'; exact h'
    have hdvd : (f : ℤ) ∣ (nb : ℤ) := by
      refine (hzc.pow_right (n := 2)).dvd_of_dvd_mul_right ?_
      exact ⟨(nb : ℤ) * f + na * e + nc * f - e, by linear_combination -hz⟩
    obtain ⟨k, hk⟩ := exists_of_dvd_sub f nb 0 hf0 (by simpa using hdvd)
    rw [Nat.zero_add] at hk
    rcases Nat.eq_zero_or_pos k with hk0 | hkp
    · subst hk0
      simp only [Nat.mul_zero] at hk
      subst hk
      simp only [Nat.zero_mul, Nat.add_zero] at h
      have hcan : f * (na * e + nc * f) = f * e := by
        have h1 : f * (na * e + nc * f) = na * (e * f) + nc * f ^ 2 := by ring
        have h2 : f * e = e * f := by ring
        rw [h1, h2]; exact h
      have hlev : na * e + nc * f = e := Nat.eq_of_mul_eq_mul_left hf0 hcan
      have hnc : nc = 0 := by
        by_contra hc2
        have : f ≤ nc * f := Nat.le_mul_of_pos_left _ (by omega)
        omega
      subst hnc
      simp only [Nat.zero_mul, Nat.add_zero] at hlev
      have hna : na = 1 := by
        rcases Nat.lt_or_ge na 2 with h2 | h2
        · interval_cases na <;> omega
        · exfalso
          have : 2 * e ≤ na * e := Nat.mul_le_mul_right _ h2
          omega
      omega
    · have hnbf : f ≤ nb := by
        have : f * 1 ≤ f * k := Nat.mul_le_mul_left _ hkp
        omega
      have h1 : f * B ≤ nb * B := Nat.mul_le_mul_right _ hnbf
      have h2 : e * f < f * B := by nlinarith [hBe, hf0]
      omega
  · -- `= b` : mod `f` gives `f ∣ n_b − 1`; `n_b ≥ 1+f` overshoots; `n_b = 1` kills the rest
    intro h
    have hz : (na : ℤ) * ((e : ℤ) * f) + (nb : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2)
        + (nc : ℤ) * (f : ℤ) ^ 2 = (f : ℤ) ^ 2 - (e : ℤ) ^ 2 := by
      have h' : (na : ℤ) * ((e : ℤ) * f) + (nb : ℤ) * (B : ℤ) + (nc : ℤ) * (f : ℤ) ^ 2
          = (B : ℤ) := by exact_mod_cast h
      rw [hBz] at h'; exact h'
    have hdvd : (f : ℤ) ∣ ((nb : ℤ) - 1) := by
      refine (hzc.pow_right (n := 2)).dvd_of_dvd_mul_right ?_
      exact ⟨(nb : ℤ) * f + na * e + nc * f - f, by linear_combination -hz⟩
    obtain ⟨k, hk⟩ := exists_of_dvd_sub f nb 1 hf1 hdvd
    rcases Nat.eq_zero_or_pos k with hk0 | hkp
    · subst hk0
      simp only [Nat.mul_zero, Nat.add_zero] at hk
      subst hk
      simp only [Nat.one_mul] at h
      have hna : na = 0 := by
        by_contra hcc
        have : e * f ≤ na * (e * f) := Nat.le_mul_of_pos_left _ (by omega)
        omega
      have hnc : nc = 0 := by
        by_contra hcc
        have h1 : f ^ 2 ≤ nc * f ^ 2 := Nat.le_mul_of_pos_left _ (by omega)
        have h2 : 0 < f ^ 2 := by positivity
        omega
      omega
    · have hnbf : 1 + f ≤ nb := by
        have : f * 1 ≤ f * k := Nat.mul_le_mul_left _ hkp
        omega
      have h1 : (1 + f) * B ≤ nb * B := Nat.mul_le_mul_right _ hnbf
      have h2 : B < (1 + f) * B := by nlinarith [hBe, he, hf1]
      omega

/-- **No common junction on `[0, f²)`** (alignment lemma, arithmetic half; unconditional).  On the
mismatch apex ray the far side advances by whole `b`-edges (junctions at `k·b`) while the near side is
`T2`'s single `c`-edge; this lemma shows the two never share a junction strictly inside the near
`c`-edge: `k·b` (`1 ≤ k ≤ f−1`) is never `n_a·ef + n_b·b + n_c·f²` with `n_c ≥ 1`.  Size-free:
`f ∣ (k−n_b)` (mod-`f`, coprime), and then the equation forces the quotient `s ≥ 1`, so `k ≥ f`. -/
theorem far_near_disjoint (e f k na nb nc B : ℕ) (hcop : Nat.Coprime e f) (hef : e < f)
    (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ f) (hB : B + e ^ 2 = f ^ 2) (hnc : 1 ≤ nc) :
    k * B ≠ na * (e * f) + nb * B + nc * f ^ 2 := by
  intro h
  have hf0 : 0 < f := by omega
  have hf0' : (0 : ℤ) < (f : ℤ) := by exact_mod_cast hf0
  have hzc : IsCoprime (f : ℤ) (e : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr hcop.symm
  have hBz : (B : ℤ) = (f : ℤ) ^ 2 - (e : ℤ) ^ 2 := by
    have hc : ((B : ℤ)) + (e : ℤ) ^ 2 = (f : ℤ) ^ 2 := by exact_mod_cast hB
    linarith
  have hz : (k : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2)
      = (na : ℤ) * ((e : ℤ) * f) + (nb : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) + (nc : ℤ) * (f : ℤ) ^ 2 := by
    have h' : (k : ℤ) * (B : ℤ)
        = (na : ℤ) * ((e : ℤ) * f) + (nb : ℤ) * (B : ℤ) + (nc : ℤ) * (f : ℤ) ^ 2 := by
      exact_mod_cast h
    rw [hBz] at h'; exact h'
  have hdvd : (f : ℤ) ∣ ((k : ℤ) - nb) := by
    refine (hzc.pow_right (n := 2)).dvd_of_dvd_mul_right ?_
    exact ⟨((k : ℤ) - nb) * f - na * e - nc * f, by linear_combination -hz⟩
  obtain ⟨s, hs⟩ := hdvd
  -- `s·B = na·e + nc·f`
  have hef' : (e : ℤ) < (f : ℤ) := by exact_mod_cast hef
  have hBpos : (0 : ℤ) < (f : ℤ) ^ 2 - (e : ℤ) ^ 2 := by nlinarith [hef', Int.natCast_nonneg e]
  have hsB : s * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) = (na : ℤ) * e + (nc : ℤ) * f := by
    have hkeq : (k : ℤ) = nb + f * s := by linarith
    have h2 : (f : ℤ) * (s * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2)) = (f : ℤ) * ((na : ℤ) * e + (nc : ℤ) * f) := by
      rw [hkeq] at hz; linear_combination hz
    exact mul_left_cancel₀ (ne_of_gt hf0') h2
  have hncz : (1 : ℤ) ≤ (nc : ℤ) := by exact_mod_cast hnc
  have hrhs : (0 : ℤ) < (na : ℤ) * e + (nc : ℤ) * f := by
    have h0 : (0 : ℤ) ≤ (na : ℤ) * e := mul_nonneg (Int.natCast_nonneg na) (Int.natCast_nonneg e)
    nlinarith [hncz, hf0']
  have hspos : 0 < s := by
    by_contra hc
    push_neg at hc
    have : s * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by omega) (le_of_lt hBpos)
    linarith [hsB]
  have hkf : (k : ℤ) + 1 ≤ (f : ℤ) := by exact_mod_cast hk2
  nlinarith [hspos, Int.natCast_nonneg nb, hf0', hs]

/-- **`V = f²` is always pierced** (alignment lemma, corner half; `e ≥ 2`).  The far side's junctions
sit at multiples of `b = f²−e²`, and `b ∤ f²`: `b ∣ f²` would give `b ∣ e²`, so `b ∣ \gcd(f²,e²)=1`,
forcing `b = 1`, impossible as `b ≥ 2e+1 ≥ 5`.  Hence no far junction lands on `V`. -/
theorem b_not_dvd_fsq (e f B : ℕ) (hcop : Nat.Coprime e f) (hef : e < f) (he : 2 ≤ e)
    (hB : B + e ^ 2 = f ^ 2) : ¬ B ∣ f ^ 2 := by
  intro hdvd
  have hBe : B ∣ e ^ 2 := by
    have h1 : B ∣ (B + e ^ 2) := hB ▸ hdvd
    exact (Nat.dvd_add_right (dvd_refl B)).mp h1
  have hcop2 : Nat.Coprime (f ^ 2) (e ^ 2) := Nat.Coprime.pow 2 2 hcop.symm
  have hg : B ∣ Nat.gcd (f ^ 2) (e ^ 2) := Nat.dvd_gcd hdvd hBe
  have hg1 : B ∣ 1 := hcop2 ▸ hg
  have hBle : B ≤ 1 := Nat.le_of_dvd one_pos hg1
  nlinarith [hef, he]

/-- **The far side is `b^f`** (alignment lemma, uniqueness; `e ≥ 2`).  Given the first far edge is
`T1`'s `b`-edge (`thm:pierce`), the whole far side is `f` copies of `b`: the only representation of the
ray length `f·b` as `n_a·ef + n_b·b + n_c·f²` with `n_b ≥ 1` is `(0, f, 0)`.  (`f ∣ n_b`, and `n_b ≤ f`
by size, so `n_b ∈ {0,f}`; `n_b ≥ 1` gives `n_b = f`, then the rest vanishes.) -/
theorem far_is_bpow (e f na nb nc B : ℕ) (hcop : Nat.Coprime e f) (hef : e < f) (he : 2 ≤ e)
    (hB : B + e ^ 2 = f ^ 2) (hb1 : 1 ≤ nb)
    (h : f * B = na * (e * f) + nb * B + nc * f ^ 2) :
    na = 0 ∧ nb = f ∧ nc = 0 := by
  have hf0 : 0 < f := by omega
  have hzc : IsCoprime (f : ℤ) (e : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr hcop.symm
  have hBz : (B : ℤ) = (f : ℤ) ^ 2 - (e : ℤ) ^ 2 := by
    have hc : ((B : ℤ)) + (e : ℤ) ^ 2 = (f : ℤ) ^ 2 := by exact_mod_cast hB
    linarith
  have hz : (f : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2)
      = (na : ℤ) * ((e : ℤ) * f) + (nb : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) + (nc : ℤ) * (f : ℤ) ^ 2 := by
    have h' : (f : ℤ) * (B : ℤ)
        = (na : ℤ) * ((e : ℤ) * f) + (nb : ℤ) * (B : ℤ) + (nc : ℤ) * (f : ℤ) ^ 2 := by
      exact_mod_cast h
    rw [hBz] at h'; exact h'
  have hdvd : (f : ℤ) ∣ (nb : ℤ) := by
    refine (hzc.pow_right (n := 2)).dvd_of_dvd_mul_right ?_
    exact ⟨(nb : ℤ) * f - ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) + na * e + nc * f, by linear_combination hz⟩
  obtain ⟨t, ht⟩ := exists_of_dvd_sub f nb 0 hf0 (by simpa using hdvd)
  rw [Nat.zero_add] at ht
  have hBpos : 0 < B := by nlinarith [hB, hef, he]
  have hnbf : nb ≤ f := by
    by_contra hc
    push_neg at hc
    have h1 : (f + 1) * B ≤ nb * B := Nat.mul_le_mul_right _ (by omega)
    have h2 : f * B < (f + 1) * B := by nlinarith [hBpos]
    have h3 : nb * B ≤ na * (e * f) + nb * B + nc * f ^ 2 := by omega
    omega
  have hnbeq : nb = f := by
    rcases Nat.eq_zero_or_pos t with h0 | hp
    · subst h0; simp only [Nat.mul_zero] at ht; omega
    · have hge : f ≤ f * t := Nat.le_mul_of_pos_right f hp
      omega
  -- with `n_b = f` the whole `B` term matches the LHS, so `na·ef + nc·f² = 0`
  have hrest : na * (e * f) + nc * f ^ 2 = 0 := by
    have hnbz : (nb : ℤ) = (f : ℤ) := by exact_mod_cast hnbeq
    rw [hnbz] at hz
    have : ((na * (e * f) + nc * f ^ 2 : ℕ) : ℤ) = 0 := by push_cast; linarith
    exact_mod_cast this
  have hef2 : 0 < e * f := Nat.mul_pos (by omega) hf0
  have hf2 : 0 < f ^ 2 := by positivity
  refine ⟨?_, hnbeq, ?_⟩
  · rcases Nat.eq_zero_or_pos na with h0 | hp
    · exact h0
    · exfalso; have : e * f ≤ na * (e * f) := Nat.le_mul_of_pos_left _ hp; omega
  · rcases Nat.eq_zero_or_pos nc with h0 | hp
    · exact h0
    · exfalso; have : f ^ 2 ≤ nc * f ^ 2 := Nat.le_mul_of_pos_left _ hp; omega

end Erdos634.BaseBetaWalks

#print axioms Erdos634.BaseBetaWalks.exists_of_dvd_sub
#print axioms Erdos634.BaseBetaWalks.base_walk_param
#print axioms Erdos634.BaseBetaWalks.side_walk_param
#print axioms Erdos634.BaseBetaWalks.base_trichotomy
#print axioms Erdos634.BaseBetaWalks.side_dichotomy
#print axioms Erdos634.BaseBetaWalks.base_trichotomy_cfree
#print axioms Erdos634.BaseBetaWalks.side_no_b
#print axioms Erdos634.BaseBetaWalks.base_b_bound
#print axioms Erdos634.BaseBetaWalks.gamma_injection
#print axioms Erdos634.BaseBetaWalks.c_edge_exists
#print axioms Erdos634.BaseBetaWalks.apex_leftover_nonrepresentable
#print axioms Erdos634.BaseBetaWalks.pierced_corner_types
#print axioms Erdos634.BaseBetaWalks.pre_pierce_dichotomy
#print axioms Erdos634.BaseBetaWalks.edge_ab_unsplittable
#print axioms Erdos634.BaseBetaWalks.far_near_disjoint
#print axioms Erdos634.BaseBetaWalks.b_not_dvd_fsq
#print axioms Erdos634.BaseBetaWalks.far_is_bpow
