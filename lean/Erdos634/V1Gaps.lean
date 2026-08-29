import Mathlib.Tactic

/-!
# Draft: the three arithmetic kills of the V₁ repair (agent session 2026-08-29)

For the column walk `(0,e,2e)` at a coprime member `(e,f)` with `f > 2e`, the induction step of
`thm:n1` at the FIRST interior point `V₁` closes by three Diophantine facts about the numerical
semigroup `⟨a,b,c⟩ = ⟨ef, f²−e², f²⟩`, proved here.  Geometry consumed elsewhere:
`pin_angle_sum` / `pin_angle_sum_interior`, `vertex_multiplicities`, through-exclusivity, the
blocked-end run equation, plus the corpus gaps `gap_b_sub_a`, `gap_e_squared`,
`RogueChord.tvertex_forcing`, and `b`-unsplittability.

* `N1_overrun_stub_gap` — `f² − 2e² ∉ ⟨a,b,c⟩`: the whole-edge closure of the chord-extension
  segment `[T,W]` left by the pure overrun (`t = e²`) does not exist.
* `N3_c_rep_unique` — for `e ≥ 2` the only representation of `c` is a single `c`: the level
  stretch `[V₀,V₁]` under a blocked junction is a single whole `c`-edge (fails at `e = 1`,
  where `c = f·a` — exactly the CRUX-1 dichotomy).
* `N2_master_through_kill` — no through-edge configuration closes: whole edges `σ`, then one
  edge of length `L ∈ {a,b,c}` covering `s = b − σ ∈ (0,L)` of the chord and overrunning `V₁`
  by `t = L − s`, needs `σ + L + x·a = 2b` for some `x ≥ 0` (the `[T′,W]` closure is forced
  into `⟨a⟩` by size); this has no solution.

All contradictions bottom out in `f ∣ e²` or `f ∣ 2e²` against `gcd(e,f) = 1`, `f > 2e` — the
divisibilities that go the OTHER way at `e = 1`.
-/

namespace Erdos634.V1Gaps

/-- Divisibility extraction: from `k·(ef) + c₀·e² = m·f²` conclude `f ∣ c₀·e²`. -/
private lemma f_dvd_of_eq (e f k m c0 : ℕ)
    (h : k * (e * f) + c0 * (e * e) = m * (f * f)) : f ∣ c0 * (e * e) := by
  have hz : (f : ℤ) ∣ ((c0 * (e * e) : ℕ) : ℤ) := by
    refine ⟨(m : ℤ) * f - k * e, ?_⟩
    push_cast
    push_cast at h
    linarith
  exact_mod_cast hz

/-- From `f ∣ 2e²`, coprimality, and `2e < f`: contradiction. -/
private lemma no_f_dvd_two_e_sq (e f : ℕ) (he : 1 ≤ e) (hef : 2 * e < f)
    (hco : Nat.Coprime e f) (h : f ∣ 2 * (e * e)) : False := by
  have hfe : Nat.Coprime f e := hco.symm
  have hfe2 : Nat.Coprime f (e * e) := hfe.mul_right hfe
  have h2 : f ∣ 2 := (Nat.Coprime.dvd_of_dvd_mul_right hfe2) h
  have := Nat.le_of_dvd (by norm_num) h2
  omega

/-- From `f ∣ e²`, coprimality, and `2e < f`: contradiction. -/
private lemma no_f_dvd_e_sq (e f : ℕ) (he : 1 ≤ e) (hef : 2 * e < f)
    (hco : Nat.Coprime e f) (h : f ∣ e * e) : False := by
  have hfe : Nat.Coprime f e := hco.symm
  have hfe2 : Nat.Coprime f (e * e) := hfe.mul_right hfe
  have h1 : f = 1 := Nat.Coprime.eq_one_of_dvd hfe2 h
  omega

/-- **N1.**  `x·ef + y·(f²−e²) + z·f² = f² − 2e²` has no solution for coprime `(e,f)`,
`f > 2e`.  (Stated additively: `d + 2e² = f²` and `b + e² = f²`.) -/
theorem N1_overrun_stub_gap (e f b d x y z : ℕ)
    (he : 1 ≤ e) (hef : 2 * e < f) (hco : Nat.Coprime e f)
    (hb : b + e * e = f * f) (hd : d + 2 * (e * e) = f * f)
    (h : x * (e * f) + y * b + z * (f * f) = d) : False := by
  have hE : 0 < e * e := by positivity
  have hdb : d < b := by omega
  have hy : y = 0 := by
    by_contra hy0
    have h1 : 1 ≤ y := Nat.one_le_iff_ne_zero.mpr hy0
    have : b ≤ y * b := Nat.le_mul_of_pos_left b h1
    omega
  subst hy
  have hz : z = 0 := by
    by_contra hz0
    have h1 : 1 ≤ z := Nat.one_le_iff_ne_zero.mpr hz0
    have : f * f ≤ z * (f * f) := Nat.le_mul_of_pos_left _ h1
    omega
  subst hz
  have key : x * (e * f) + 2 * (e * e) = 1 * (f * f) := by omega
  exact no_f_dvd_two_e_sq e f he hef hco (f_dvd_of_eq e f x 1 2 key)

/-- **N3.**  For `e ≥ 2` (coprime, `f > 2e`) the only representation
`x·ef + y·(f²−e²) + z·f² = f²` is `(x,y,z) = (0,0,1)`. -/
theorem N3_c_rep_unique (e f b x y z : ℕ)
    (he : 2 ≤ e) (hef : 2 * e < f) (hco : Nat.Coprime e f)
    (hb : b + e * e = f * f)
    (h : x * (e * f) + y * b + z * (f * f) = f * f) :
    x = 0 ∧ y = 0 ∧ z = 1 := by
  have hE : 0 < e * e := by positivity
  have hff : 0 < f * f := by omega
  have hbpos : 0 < b := by
    -- b = f² − e² > 0 since e < f ≤ f²… from hb and e*e < f*f
    have h4 : 2 * e * (2 * e) < f * f :=
      mul_lt_mul'' hef hef (by omega) (by omega)
    have h5 : 2 * e * (2 * e) = 4 * (e * e) := by ring
    omega
  have h4 : 4 * (e * e) < f * f := by
    have := mul_lt_mul'' hef hef (by omega : 0 ≤ 2 * e) (by omega : 0 ≤ 2 * e)
    have h5 : 2 * e * (2 * e) = 4 * (e * e) := by ring
    omega
  have hz1 : z ≤ 1 := by
    by_contra hz
    push_neg at hz
    have h2 : 2 * (f * f) ≤ z * (f * f) := Nat.mul_le_mul_right (f * f) hz
    omega
  interval_cases z
  · -- z = 0 : x·ef + y·b = f²
    exfalso
    have hy1 : y ≤ 1 := by
      by_contra hy
      push_neg at hy
      have h2b : 2 * b ≤ y * b := Nat.mul_le_mul_right b hy
      omega
    interval_cases y
    · -- y = 0 : x·ef = f², so e ∣ f, dead by coprimality and e ≥ 2
      have hh : x * (e * f) = f * f := by omega
      have hdvd : e ∣ f * f := ⟨x * f, by rw [← hh]; ring⟩
      have hef' : e ∣ f := hco.dvd_of_dvd_mul_right hdvd
      have h1 : e = 1 := Nat.Coprime.eq_one_of_dvd hco hef'
      omega
    · -- y = 1 : x·ef = e², so x·f = e, dead by e < f
      have hh : x * (e * f) = e * e := by omega
      have h2 : e * (x * f) = e * e := by rw [← hh]; ring
      have hcancel : x * f = e := Nat.eq_of_mul_eq_mul_left (by omega) h2
      rcases Nat.eq_zero_or_pos x with h0 | h1
      · subst h0; omega
      · have : f ≤ x * f := Nat.le_mul_of_pos_left f h1
        omega
  · -- z = 1 : x·ef + y·b = 0
    have hx0 : x * (e * f) = 0 := by omega
    have hy0 : y * b = 0 := by omega
    refine ⟨?_, ?_, rfl⟩
    · rcases Nat.mul_eq_zero.mp hx0 with h0 | h0
      · exact h0
      · exfalso
        have : 0 < e * f := Nat.mul_pos (by omega) (by omega)
        omega
    · rcases Nat.mul_eq_zero.mp hy0 with h0 | h0
      · exact h0
      · omega

/-- **N2 (master through-kill).**  No `σ = p·a + q·b + r·c`, `L ∈ {a,b,c}`, `x ≥ 0` satisfy
`σ + L + x·a = 2b` together with `σ < b < σ + L`  (the through-edge covers a positive part
`s = b − σ` of the chord, `0 < s < L`, and the closure of `[T′,W]` is `x·a = b − t`).
Coprime `(e,f)`, `f > 2e`. -/
theorem N2_master_through_kill (e f b p q r L x : ℕ)
    (he : 1 ≤ e) (hef : 2 * e < f) (hco : Nat.Coprime e f)
    (hb : b + e * e = f * f)
    (hL : L = e * f ∨ L = b ∨ L = f * f)
    (hs1 : p * (e * f) + q * b + r * (f * f) < b)
    (hs2 : b < p * (e * f) + q * b + r * (f * f) + L)
    (h : p * (e * f) + q * b + r * (f * f) + L + x * (e * f) = 2 * b) : False := by
  have hE : 0 < e * e := by positivity
  have hff : 0 < f * f := by omega
  have hq : q = 0 := by
    by_contra hq0
    have h1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq0
    have : b ≤ q * b := Nat.le_mul_of_pos_left b h1
    omega
  subst hq
  rcases hL with hL | hL | hL
  all_goals subst hL
  · -- L = a = ef
    have hr : r ≤ 1 := by
      by_contra hr0
      push_neg at hr0
      have h2 : 2 * (f * f) ≤ r * (f * f) := Nat.mul_le_mul_right (f * f) hr0
      omega
    have hsplit : (p + x + 1) * (e * f) = p * (e * f) + (e * f) + x * (e * f) := by ring
    interval_cases r
    · -- r = 0 : (p+x+1)·ef + 2e² = 2f²
      have key : (p + x + 1) * (e * f) + 2 * (e * e) = 2 * (f * f) := by omega
      exact no_f_dvd_two_e_sq e f he hef hco (f_dvd_of_eq e f (p + x + 1) 2 2 key)
    · -- r = 1 : (p+x+1)·ef + 2e² = f²
      have key : (p + x + 1) * (e * f) + 2 * (e * e) = 1 * (f * f) := by omega
      exact no_f_dvd_two_e_sq e f he hef hco (f_dvd_of_eq e f (p + x + 1) 1 2 key)
  · -- L = b : σ + x·a = b, so (p+x)·ef + e² = f²
    have hr : r = 0 := by
      by_contra hr0
      have h1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr0
      have : f * f ≤ r * (f * f) := Nat.le_mul_of_pos_left _ h1
      omega
    subst hr
    have hsplit : (p + x) * (e * f) = p * (e * f) + x * (e * f) := by ring
    have key : (p + x) * (e * f) + 1 * (e * e) = 1 * (f * f) := by omega
    have := f_dvd_of_eq e f (p + x) 1 1 key
    rw [Nat.one_mul] at this
    exact no_f_dvd_e_sq e f he hef hco this
  · -- L = c = f² : (p+x)·ef + 2e² = f²
    have hr : r = 0 := by
      by_contra hr0
      have h1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr0
      have : f * f ≤ r * (f * f) := Nat.le_mul_of_pos_left _ h1
      omega
    subst hr
    have hsplit : (p + x) * (e * f) = p * (e * f) + x * (e * f) := by ring
    have key : (p + x) * (e * f) + 2 * (e * e) = 1 * (f * f) := by omega
    exact no_f_dvd_two_e_sq e f he hef hco (f_dvd_of_eq e f (p + x) 1 2 key)

end Erdos634.V1Gaps

#print axioms Erdos634.V1Gaps.N1_overrun_stub_gap
#print axioms Erdos634.V1Gaps.N2_master_through_kill
#print axioms Erdos634.V1Gaps.N3_c_rep_unique
