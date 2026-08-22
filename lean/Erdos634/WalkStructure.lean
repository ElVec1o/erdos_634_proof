import Mathlib.Tactic

/-!
# The boundary walk structure at `m = 1`, formalized

Erdős #634 — lifting companion (iii) and (iv) from PROVED to VERIFIED.

`BaseWord.lean` derives the base-word family from two companion facts taken as hypotheses:

* **(iii)** no equal side carries a `b`-edge, so every boundary `b`-edge lies on the base;
* **(iv)** the base `b`-count is `Q = e + f j` with `j (f - e) ≤ e - 1`.

Both are proved on paper in the companion, and their proofs are pure integer arithmetic.  This file
supplies them, so the base-word family and the `Q = e` pin no longer rest on an unformalized link.

## What the proofs are

For the **base**, the walk `P a + Q b + R c = e N₀` with `(a,b,c) = (ef, f²-e², f²)` and
`N₀ = 3f² - e²` reduces mod `f` to `Q e² ≡ e³`, so `f ∣ Q - e` by coprimality, and `Q = e + f j`
(`base_Q_residue`).  Substituting and cancelling one `f` gives the halved equation

  `P e + j (f² - e²) + R f = 2 e f`   (`base_halved`),

whose own reduction mod `f` gives `f ∣ P - j e`, so `P = j e + f p`, and cancelling `f` again leaves
the level equation `p e + j f + R = 2 e` (`base_level`).

For the **side**, the same reduction on `P a + Q b + R c = f³` gives `Q e² ≡ 0`, hence `f ∣ Q`
(`side_Q_residue`), and the level equation `p e + q f + R = f`.

The bounds then follow from nonnegativity of `P`.  If `q ≥ 1` then `f p ≥ -q e > -q f`, so
`p ≥ 1 - q`, and `R = f - p e - q f ≤ (1-q)(f-e) ≤ 0`, contradicting `R ≥ 1`: hence `q = 0`, which is
**(iii)** (`side_no_b`).  Identically on the base, `j ≥ 1` gives `p ≥ 1 - j` and
`R ≤ e - j(f - e)`, so `R ≥ 1` forces `j (f - e) ≤ e - 1`, which is **(iv)** (`base_j_bound`).

## The hypothesis (iv) actually needs, and where it does not apply

Both bounds consume `R ≥ 1` — the `γ`-trap, i.e. the walk carries at least one `c`-edge.  On the
side that is automatic.  On the **base** it is not: the corner rule (one tile per base corner, `β`
between edges `a` and `c`) permits `R = 0`, and `R = 0` is exactly the complete-corner-wall
configuration of `hyp:walls`.  So (iv) is silent on the `hyp:walls` word itself.

`base_R_zero_bound` handles that case: with `R = 0` the level equation is `p e + j f = 2 e`, and
`P ≥ 0` gives `j (f² - e²) ≤ 2 e f`.  That bound is *not* `j ≤ 1` — at `(5,6)` it permits `j ≤ 5`,
and `j = 5` is realized by `a¹ b³⁵ c⁰`, a genuine base word absent from both the original `N = 83`
search and the first census here.  The complete base-word set at `(5,6)` has **eight** members, not
five and not seven.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.WalkStructure

/-! ### The base walk -/

/-- **`f ∣ Q - e`.**  Reducing `P(ef) + Q(f² - e²) + R f² = e(3f² - e²)` mod `f` leaves
`Q e² ≡ e³`, and `gcd(e,f) = 1` cancels `e²`. -/
theorem base_Q_residue (e f P Q R : ℤ) (hcop : IsCoprime e f)
    (h : P * (e * f) + Q * (f ^ 2 - e ^ 2) + R * f ^ 2 = e * (3 * f ^ 2 - e ^ 2)) :
    f ∣ Q - e := by
  have hd : f ∣ (Q - e) * e ^ 2 := ⟨P * e + Q * f + R * f - 3 * e * f, by ring_nf; ring_nf at h; linarith⟩
  exact (hcop.symm.pow_right (n := 2)).dvd_of_dvd_mul_right hd

/-- **The halved equation.**  With `Q = e + f j`, one factor `f` cancels. -/
theorem base_halved (e f P R j : ℤ) (hf : f ≠ 0)
    (h : P * (e * f) + (e + f * j) * (f ^ 2 - e ^ 2) + R * f ^ 2 = e * (3 * f ^ 2 - e ^ 2)) :
    P * e + j * (f ^ 2 - e ^ 2) + R * f = 2 * e * f := by
  have : f * (P * e + j * (f ^ 2 - e ^ 2) + R * f) = f * (2 * e * f) := by
    ring_nf; ring_nf at h; linarith
  exact mul_left_cancel₀ hf this

/-- **`f ∣ P - j e`.**  Reducing the halved equation mod `f`. -/
theorem base_P_residue (e f P R j : ℤ) (hcop : IsCoprime e f)
    (h : P * e + j * (f ^ 2 - e ^ 2) + R * f = 2 * e * f) : f ∣ P - j * e := by
  have hd : f ∣ (P - j * e) * e := ⟨2 * e - j * f - R, by ring_nf; ring_nf at h; linarith⟩
  exact hcop.symm.dvd_of_dvd_mul_right hd

/-- **The level equation.**  With `P = j e + f p`, cancelling `f` again gives
`p e + j f + R = 2 e`. -/
theorem base_level (e f P R j p : ℤ) (hf : f ≠ 0) (hP : P = j * e + f * p)
    (h : P * e + j * (f ^ 2 - e ^ 2) + R * f = 2 * e * f) : p * e + j * f + R = 2 * e := by
  subst hP
  have : f * (p * e + j * f + R) = f * (2 * e) := by ring_nf; ring_nf at h; linarith
  exact mul_left_cancel₀ hf this

/-- **Companion (iv).**  If the base carries a `c`-edge (`R ≥ 1`) and `j ≥ 1`, then
`j (f - e) ≤ e - 1`.  Proof: `P = j e + f p ≥ 0` with `e < f` gives `f p ≥ -j e > -j f`, so
`p ≥ 1 - j`, and the level equation yields `R ≤ e - j(f - e)`. -/
theorem base_j_bound (e f P R j p : ℤ) (he : 1 ≤ e) (hef : e < f) (hP0 : 0 ≤ P)
    (hP : P = j * e + f * p) (hR : 1 ≤ R) (hj : 1 ≤ j)
    (hlev : p * e + j * f + R = 2 * e) : j * (f - e) ≤ e - 1 := by
  have hf : 0 < f := lt_trans (by omega) hef
  -- p ≥ 1 - j
  have hp : 1 - j ≤ p := by nlinarith
  -- R ≤ e - j(f-e)
  nlinarith

/-- **(iv) holds trivially at `j = 0`**, since `e ≥ 1`. -/
theorem base_j_bound_zero (e f : ℤ) (he : 1 ≤ e) : (0 : ℤ) * (f - e) ≤ e - 1 := by simp; omega

/-! ### The side walk -/

/-- **`f ∣ Q` on a side.**  Reducing `P(ef) + Q(f² - e²) + R f² = f³` mod `f` leaves `Q e² ≡ 0`. -/
theorem side_Q_residue (e f P Q R : ℤ) (hcop : IsCoprime e f)
    (h : P * (e * f) + Q * (f ^ 2 - e ^ 2) + R * f ^ 2 = f ^ 3) : f ∣ Q := by
  have hd : f ∣ Q * e ^ 2 := ⟨P * e + Q * f + R * f - f ^ 2, by ring_nf; ring_nf at h; linarith⟩
  exact (hcop.symm.pow_right (n := 2)).dvd_of_dvd_mul_right hd

/-- The side level equation: with `Q = f q` and `P = q e + f p`, `p e + q f + R = f`. -/
theorem side_level (e f P R q p : ℤ) (hf : f ≠ 0) (hP : P = q * e + f * p)
    (h : P * (e * f) + (f * q) * (f ^ 2 - e ^ 2) + R * f ^ 2 = f ^ 3) :
    p * e + q * f + R = f := by
  subst hP
  have : (f * f) * (p * e + q * f + R) = (f * f) * f := by ring_nf; ring_nf at h; linarith
  have hff : (f * f) ≠ 0 := mul_ne_zero hf hf
  exact mul_left_cancel₀ hff this

/-- **Companion (iii): the equal sides carry no `b`-edge.**  `q ≥ 1` would give `p ≥ 1 - q` and
hence `R ≤ (1-q)(f-e) ≤ 0`, contradicting the `γ`-trap `R ≥ 1`. -/
theorem side_no_b (e f P R q p : ℤ) (he : 1 ≤ e) (hef : e < f) (hP0 : 0 ≤ P)
    (hP : P = q * e + f * p) (hR : 1 ≤ R) (hq : 0 ≤ q)
    (hlev : p * e + q * f + R = f) : q = 0 := by
  have hf : 0 < f := lt_trans (by omega) hef
  by_contra hne
  have hq1 : 1 ≤ q := by omega
  have hp : 1 - q ≤ p := by nlinarith
  nlinarith

/-! ### The case (iv) does not cover: `R = 0` on the base -/

/-- **`R = 0` bounds `j` by `j (f² - e²) ≤ 2 e f`.**  Multiplying the level equation
`p e + j f = 2 e` by `f` and using `f p ≥ -j e` from `P ≥ 0` gives
`2 e f = p e f + j f² ≥ -j e² + j f²`.

An earlier version of this file claimed `j ≤ 1` here.  That is **false**: at `(e,f) = (5,6)` the
bound permits `j ≤ 5`, and `j = 5` is realized by the genuine base word `a¹ b³⁵ c⁰`, which was
missing from both the original `N = 83` search and from the first census in `BaseWord.lean`.
Companion (iv) does not cover it because (iv)'s proof consumes `R ≥ 1`. -/
theorem base_R_zero_bound (e f P j p : ℤ) (he : 1 ≤ e) (hef : e < f) (hP0 : 0 ≤ P)
    (hP : P = j * e + f * p) (hj : 0 ≤ j) (hlev : p * e + j * f + 0 = 2 * e) :
    j * (f ^ 2 - e ^ 2) ≤ 2 * e * f := by
  have hf : 0 < f := lt_trans (by omega) hef
  have hfp : -(j * e) ≤ f * p := by linarith [hP0, hP]
  nlinarith

/-- **`R = 0`, `j = 0` gives the `hyp:walls` word.**  The level equation reads `p e = 2 e`, so
`p = 2` and `P = 2 f`: the base word is `a^{2f} b^e c^0`. -/
theorem base_R_zero_word (e f P p : ℤ) (he : 1 ≤ e) (hP : P = 0 * e + f * p)
    (hlev : p * e + 0 * f + 0 = 2 * e) : p = 2 ∧ P = 2 * f := by
  have he0 : (e : ℤ) ≠ 0 := by omega
  have hp : p = 2 := by
    have : p * e = 2 * e := by linarith
    exact mul_right_cancel₀ he0 (by linarith [this])
  exact ⟨hp, by rw [hP, hp]; ring⟩

/-- **`R = 0`, `j = 1` needs `e ∣ f`, hence `e = 1`.**  The level equation gives `p e = 2e - f`,
so `e ∣ f`; with `gcd(e,f) = 1` that forces `e = 1`. -/
theorem base_R_zero_j_one (e f p : ℤ) (he : 1 ≤ e) (hcop : IsCoprime e f)
    (hlev : p * e + 1 * f + 0 = 2 * e) : e = 1 := by
  have hdvd : e ∣ f := ⟨2 - p, by linarith⟩
  have : IsUnit e := hcop.isUnit_of_dvd' (dvd_refl e) hdvd
  rcases Int.isUnit_iff.mp this with h | h <;> omega

end Erdos634.WalkStructure

#print axioms Erdos634.WalkStructure.base_Q_residue
#print axioms Erdos634.WalkStructure.base_halved
#print axioms Erdos634.WalkStructure.base_P_residue
#print axioms Erdos634.WalkStructure.base_level
#print axioms Erdos634.WalkStructure.base_j_bound
#print axioms Erdos634.WalkStructure.side_Q_residue
#print axioms Erdos634.WalkStructure.side_level
#print axioms Erdos634.WalkStructure.side_no_b
#print axioms Erdos634.WalkStructure.base_R_zero_bound
#print axioms Erdos634.WalkStructure.base_R_zero_word
#print axioms Erdos634.WalkStructure.base_R_zero_j_one
