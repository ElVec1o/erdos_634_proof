import Mathlib.Tactic

/-!
# The c-chord dichotomy (Erdős #634, base-β branch)

A chord of length `c` blocked at both ends — by the target boundary or by the interior of an
already-placed tile — has its far side partitioned into whole tile edges summing to `c`. This file
solves that walk equation, for every member: the only solutions are a single `c`-edge, or, exactly
when `e = 1`, a run of `f` a-edges.

The modular step is the explicit ℤ-identity `(y−1)·f² = e·(y·e − x·f)`, so `e ∣ (y−1)·f²`;
coprimality gives `e ∣ y−1`, the size bound gives `y ≤ e`, hence `y ∈ {0,1}`, and `y = 1` dies on
`x·f = e < f`. With `y = 0`, `x·e = f` forces `e ∣ f`, hence `e = 1` and `x = f`.
-/

namespace Erdos634.CChord

variable {e f a b c : ℕ}

/-- **c-chord dichotomy.** `x·a + y·b + z·c = c` forces `(0,0,1)`, or `e = 1` with `(f,0,0)`. -/
theorem c_chord_dichotomy (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (ha : a = e * f) (hb : b + e * e = f * f) (hc : c = f * f)
    {x y z : ℕ} (h : x * a + y * b + z * c = c) :
    (x = 0 ∧ y = 0 ∧ z = 1) ∨ (e = 1 ∧ x = f ∧ y = 0 ∧ z = 0) := by
  have ha2 : 2 ≤ a := by subst ha; nlinarith
  have hb3 : 3 ≤ b := by nlinarith
  have hcpos : 0 < c := by subst hc; nlinarith
  have hz : z ≤ 1 := by nlinarith
  interval_cases z
  · -- z = 0
    right
    simp only [Nat.zero_mul, Nat.add_zero] at h
    have hy0 : y = 0 := by
      by_contra hy
      have hy1 : 1 ≤ y := Nat.one_le_iff_ne_zero.mpr hy
      have hye : y ≤ e := by
        by_contra hye'
        have h1 : e + 1 ≤ y := by omega
        have h2 : (e + 1) * b ≤ y * b := Nat.mul_le_mul_right b h1
        have hgt : c < (e + 1) * b := by subst hc; nlinarith
        omega
      have hkey : (y : ℤ) * ((f : ℤ) * f) + (x : ℤ) * ((e : ℤ) * f)
          = (f : ℤ) * f + (y : ℤ) * ((e : ℤ) * e) := by
        have h2 : y * b + y * (e * e) = y * (f * f) := by rw [← Nat.mul_add, hb]
        have h3 : x * (e * f) + y * b = f * f := by subst ha hc; omega
        have hnat : y * (f * f) + x * (e * f) = f * f + y * (e * e) := by omega
        exact_mod_cast hnat
      have hdvd : (e : ℤ) ∣ ((y : ℤ) - 1) * ((f : ℤ) * f) :=
        ⟨(y : ℤ) * e - (x : ℤ) * f, by linear_combination hkey⟩
      have hcopZ : IsCoprime (e : ℤ) ((f : ℤ) * f) := by
        have hn : Nat.Coprime e (f * f) := hco.mul_right hco
        have h4 := (Nat.isCoprime_iff_coprime (m := e) (n := f * f)).mpr hn
        push_cast at h4
        exact h4
      have hy_dvd : (e : ℤ) ∣ (y : ℤ) - 1 := hcopZ.dvd_of_dvd_mul_right hdvd
      obtain ⟨k, hk⟩ := hy_dvd
      have hepos : (0 : ℤ) < (e : ℤ) := by exact_mod_cast he
      have hlt : (e : ℤ) * k < (e : ℤ) * 1 := by
        have hyle : (y : ℤ) ≤ (e : ℤ) := by exact_mod_cast hye
        nlinarith [hk]
      have hge : (0 : ℤ) ≤ (e : ℤ) * k := by
        have hy1' : (1 : ℤ) ≤ (y : ℤ) := by exact_mod_cast hy1
        nlinarith [hk]
      have hk_lt : k < 1 := lt_of_mul_lt_mul_left hlt (le_of_lt hepos)
      have hk_ge : 0 ≤ k := nonneg_of_mul_nonneg_right hge hepos
      have hk0 : k = 0 := by omega
      have hy_eq : y = 1 := by
        have h5 : (y : ℤ) - 1 = 0 := by rw [hk, hk0]; ring
        have h6 : (y : ℤ) = 1 := by omega
        exact_mod_cast h6
      subst hy_eq
      have hx_ef : x * (e * f) = e * e := by subst ha hc; omega
      have hx_f : x * f = e := by
        have h5 : e * (x * f) = e * e := by rw [← hx_ef]; ring
        exact Nat.eq_of_mul_eq_mul_left (by omega) h5
      rcases Nat.eq_zero_or_pos x with h0 | h0
      · subst h0; simp at hx_f; omega
      · have h7 : f ≤ x * f := Nat.le_mul_of_pos_left f h0
        omega
    subst hy0
    simp only [Nat.zero_mul, Nat.add_zero] at h
    have hxe : x * e = f := by
      have h1 : x * (e * f) = f * f := by subst ha hc; omega
      have h2 : (x * e) * f = f * f := by rw [← h1]; ring
      exact Nat.eq_of_mul_eq_mul_right (by omega) h2
    have he_dvd : e ∣ f := ⟨x, by rw [← hxe]; ring⟩
    have he1 : e = 1 := Nat.Coprime.eq_one_of_dvd hco he_dvd
    subst he1
    simp only [Nat.mul_one] at hxe
    exact ⟨rfl, hxe, rfl, rfl⟩
  · -- z = 1
    left
    have hsum : x * a + y * b = 0 := by omega
    have hx : x = 0 := by
      rcases Nat.mul_eq_zero.mp (by omega : x * a = 0) with h0 | h0
      · exact h0
      · omega
    have hy : y = 0 := by
      rcases Nat.mul_eq_zero.mp (by omega : y * b = 0) with h0 | h0
      · exact h0
      · omega
    exact ⟨hx, hy, rfl⟩


/-- **The thick-member monochotomy.** For `e ≥ 2` (coprime to `f`, `e < f`) the far side of a
`c`-chord admits exactly ONE decomposition: a single `c`. The `e = 1` branch alternative
(`f` copies of `a`) does not exist: `xef + y(f²−e²) = f²` forces `e ∣ y−1` by coprimality, and
both `y = 1` and `y ≥ e+1` die on size. Consequently every `c`-chord fork of the corner chain is
FORCED at thick members — the chain is stiffer than at `e = 1`, not looser. -/
theorem c_chord_unique_thick {e f x y z : ℕ} (he : 2 ≤ e) (hef : e < f)
    (hco : Nat.Coprime e f)
    (h : x * (e * f) + y * (f * f - e * e) + z * (f * f) = f * f) :
    x = 0 ∧ y = 0 ∧ z = 1 := by
  have hee : e * e < f * f := by nlinarith
  have hbe : 1 ≤ f * f - e * e := by omega
  have hcoff : Nat.Coprime e (f * f) := Nat.Coprime.mul_right hco hco
  rcases Nat.lt_or_ge z 2 with hz2 | hz2
  · interval_cases z
    · -- z = 0 : x·ef + y·(f²−e²) = f²
      exfalso
      have h : x * (e * f) + y * (f * f - e * e) = f * f := by omega
      rcases Nat.eq_zero_or_pos y with hy0 | hy1
      · subst hy0
        simp only [Nat.zero_mul, Nat.add_zero] at h
        have hdvd : e ∣ f * f := by
          rw [← h]; exact ⟨x * f, by ring⟩
        have hg := Nat.dvd_gcd (dvd_refl e) hdvd
        rw [Nat.coprime_iff_gcd_eq_one.mp hcoff] at hg
        have := Nat.le_of_dvd (by norm_num) hg; omega
      · -- y ≥ 1: key identity (y−1)·f² + x·ef = y·e²
        obtain ⟨w, rfl⟩ : ∃ w, y = w + 1 := ⟨y - 1, by omega⟩
        have hexp : (w + 1) * (f * f - e * e) + (w + 1) * (e * e) = (w + 1) * (f * f) := by
          rw [← Nat.mul_add]; congr 1; omega
        have hw1 : w * (f * f) + (f * f) = (w + 1) * (f * f) := by ring
        have hkey : w * (f * f) + x * (e * f) = (w + 1) * (e * e) := by omega
        have hd1 : e ∣ (w + 1) * (e * e) := ⟨(w + 1) * e, by ring⟩
        have hd2 : e ∣ x * (e * f) := ⟨x * f, by ring⟩
        have hd3 : e ∣ w * (f * f) := by
          have h6 := Nat.dvd_sub hd1 hd2
          have h7 : (w + 1) * (e * e) - x * (e * f) = w * (f * f) := by omega
          rwa [h7] at h6
        have hdw : e ∣ w := (Nat.Coprime.dvd_of_dvd_mul_right hcoff) hd3
        rcases Nat.eq_zero_or_pos w with hw0 | hwpos
        · -- y = 1 : x·ef = e², so x·f = e, impossible
          subst hw0
          simp only [Nat.zero_mul, Nat.zero_add] at hkey
          have hxf : x * f = e := by
            have h9 : x * (e * f) = e * e := by omega
            have h8 : e * (x * f) = e * e := by rw [← h9]; ring
            exact Nat.eq_of_mul_eq_mul_left (by omega) h8
          rcases Nat.eq_zero_or_pos x with hx0 | hx1
          · subst hx0; simp at hxf; omega
          · have : f ≤ x * f := Nat.le_mul_of_pos_left f hx1
            omega
        · -- w ≥ 1 and e ∣ w : y = w+1 ≥ e+1, size kill
          have hwe : e ≤ w := Nat.le_of_dvd hwpos hdw
          have hsz : (e + 1) * (f * f - e * e) ≤ (w + 1) * (f * f - e * e) :=
            Nat.mul_le_mul_right _ (by omega)
          have hgt : f * f < (e + 1) * (f * f - e * e) := by
            have hfe : e + 1 ≤ f := hef
            have h9 : e * e + e < f * f := by nlinarith
            have h10 : (e + 1) * (f * f - e * e) = e * (f * f - e * e) + (f * f - e * e) := by
              ring
            nlinarith [Nat.sub_add_cancel (Nat.le_of_lt hee)]
          omega
    · -- z = 1 : x·ef + y·(f²−e²) = 0
      have hx : x * (e * f) = 0 := by omega
      have hy : y * (f * f - e * e) = 0 := by omega
      rcases Nat.mul_eq_zero.mp hx with h0 | h0
      · rcases Nat.mul_eq_zero.mp hy with h1 | h1
        · exact ⟨h0, h1, rfl⟩
        · omega
      · have : 0 < e * f := Nat.mul_pos (by omega) (by omega)
        omega
  · -- z ≥ 2
    exfalso
    have : 2 * (f * f) ≤ z * (f * f) := Nat.mul_le_mul_right _ hz2
    have hff : 0 < f * f := Nat.mul_pos (by omega) (by omega)
    omega


/-- **The thick base trichotomy.** For a separated member (`f² > 2ef + e²`) the base
`Y = e(3f²−e²)` admits exactly three edge decompositions: `(x,y,z) ∈ {(0,e,2e), (f,e,e),
(2f,e,0)}`. Modulo `f` the `b`-count is forced to `y ≡ e`, separation kills `y ≥ e+f`, and then
`xe + zf = 2ef` with `f ∣ x` leaves the three columns. The walls form is the middle one:
`f` `a`-feet, `e` `b`'s, `e` `c`-feet. -/
theorem base_trichotomy {e f x y z : ℕ} (he : 1 ≤ e) (hef : e < f)
    (hco : Nat.Coprime e f) (hsep : 2 * e * f + e * e < f * f)
    (h : x * (e * f) + y * (f * f - e * e) + z * (f * f) = e * (3 * (f * f) - e * e)) :
    (x = 0 ∧ y = e ∧ z = 2 * e) ∨ (x = f ∧ y = e ∧ z = e) ∨
    (x = 2 * f ∧ y = e ∧ z = 0) := by
  have hee : e * e < f * f := by nlinarith
  have hcof : Nat.Coprime f e := Nat.coprime_comm.mp hco
  have hcofe : Nat.Coprime f (e * e) := Nat.Coprime.mul_right hcof hcof
  -- step 1: y ≥ e and f ∣ y − e
  have hstep1 : e ≤ y ∧ f ∣ y - e := by
    rcases Nat.lt_or_ge y e with hy | hy
    · -- y < e: f | e²(e−y), coprime ⟹ f | e−y < f ⟹ contradiction
      exfalso
      have hkey : x * (e * f) + z * (f * f) + (e - y) * (e * e) + y * (f * f)
          = e * (3 * (f * f)) := by
        have hx1 : y * (f * f - e * e) + y * (e * e) = y * (f * f) := by
          rw [← Nat.mul_add]; congr 1; omega
        have hx2 : (e - y) * (e * e) + y * (e * e) = e * (e * e) := by
          rw [← Nat.add_mul]; congr 1; omega
        have hx3 : e * (3 * (f * f) - e * e) + e * (e * e) = e * (3 * (f * f)) := by
          rw [← Nat.mul_add]; congr 1; omega
        omega
      have hd : f ∣ (e - y) * (e * e) := by
        have d1 : f ∣ x * (e * f) := ⟨x * e, by ring⟩
        have d2 : f ∣ z * (f * f) := ⟨z * f, by ring⟩
        have d3 : f ∣ y * (f * f) := ⟨y * f, by ring⟩
        have d4 : f ∣ e * (3 * (f * f)) := ⟨e * 3 * f, by ring⟩
        have h5 : e * (3 * (f * f)) - x * (e * f) - z * (f * f) - y * (f * f)
            = (e - y) * (e * e) := by omega
        have h6 := Nat.dvd_sub (Nat.dvd_sub (Nat.dvd_sub d4 d1) d2) d3
        rwa [h5] at h6
      have hdey : f ∣ e - y := (Nat.Coprime.dvd_of_dvd_mul_right hcofe) hd
      have : e - y = 0 ∨ f ≤ e - y := by
        rcases Nat.eq_zero_or_pos (e - y) with h0 | h0
        · exact Or.inl h0
        · exact Or.inr (Nat.le_of_dvd h0 hdey)
      omega
    · constructor
      · exact hy
      · have hkey : x * (e * f) + z * (f * f) + y * (f * f)
            = e * (3 * (f * f)) + (y - e) * (e * e) := by
          have hx1 : y * (f * f - e * e) + y * (e * e) = y * (f * f) := by
            rw [← Nat.mul_add]; congr 1; omega
          have hx2 : (y - e) * (e * e) + e * (e * e) = y * (e * e) := by
            rw [← Nat.add_mul]; congr 1; omega
          have hx3 : e * (3 * (f * f) - e * e) + e * (e * e) = e * (3 * (f * f)) := by
            rw [← Nat.mul_add]; congr 1; omega
          omega
        have hd : f ∣ (y - e) * (e * e) := by
          have d1 : f ∣ x * (e * f) := ⟨x * e, by ring⟩
          have d2 : f ∣ z * (f * f) := ⟨z * f, by ring⟩
          have d3 : f ∣ y * (f * f) := ⟨y * f, by ring⟩
          have d4 : f ∣ e * (3 * (f * f)) := ⟨e * 3 * f, by ring⟩
          have h5 : x * (e * f) + z * (f * f) + y * (f * f) - e * (3 * (f * f))
              = (y - e) * (e * e) := by omega
          have h6 := Nat.dvd_sub (Nat.dvd_add (Nat.dvd_add d1 d2) d3) d4
          rwa [h5] at h6
        exact (Nat.Coprime.dvd_of_dvd_mul_right hcofe) hd
  obtain ⟨hye, hdvd⟩ := hstep1
  -- step 2: y = e (y ≥ e+f dies on separation)
  have hy : y = e := by
    rcases Nat.eq_zero_or_pos (y - e) with h0 | h0
    · omega
    · exfalso
      have hyef : e + f ≤ y := by
        have := Nat.le_of_dvd h0 hdvd; omega
      have hsz : (e + f) * (f * f - e * e) ≤ y * (f * f - e * e) :=
        Nat.mul_le_mul_right _ hyef
      have hbig : e * (3 * (f * f) - e * e) < (e + f) * (f * f - e * e) := by
        have h7 : (e + f) * (f * f - e * e) = e * (f * f - e * e) + f * (f * f - e * e) := by
          ring
        have h8 : e * (f * f - e * e) + e * (e * e) = e * (f * f) := by
          rw [← Nat.mul_add]; congr 1; omega
        have h9 : e * (3 * (f * f) - e * e) + e * (e * e) = e * (3 * (f * f)) := by
          rw [← Nat.mul_add]; congr 1; omega
        have h10 : f * (2 * e * f + e * e) < f * (f * f) :=
          (Nat.mul_lt_mul_left (show 0 < f by omega)).mpr hsep
        have h11 : f * (f * f - e * e) + f * (e * e) = f * (f * f) := by
          rw [← Nat.mul_add]; congr 1; omega
        nlinarith
      omega
  rw [hy] at h
  clear hye hdvd
  -- step 3: xe + zf = 2ef, f | x, three columns
  have hxz : x * e + z * f = 2 * e * f := by
    have hx1 : e * (f * f - e * e) + e * (e * e) = e * (f * f) := by
      rw [← Nat.mul_add]; congr 1; omega
    have hx3 : e * (3 * (f * f) - e * e) + e * (e * e) = e * (3 * (f * f)) := by
      rw [← Nat.mul_add]; congr 1; omega
    have b1 : e * (3 * (f * f)) = 3 * (e * (f * f)) := by ring
    rw [b1] at hx3
    have hkey : x * (e * f) + z * (f * f) = 2 * (e * (f * f)) := by omega
    have h12 : (x * e + z * f) * f = (2 * e * f) * f := by
      have hb : x * (e * f) + z * (f * f) = (x * e + z * f) * f := by ring
      have h13 : 2 * (e * (f * f)) = (2 * e * f) * f := by ring
      omega
    exact Nat.eq_of_mul_eq_mul_right (by omega) h12
  have hdx : f ∣ x := by
    have hd : f ∣ x * e := by
      have d2 : f ∣ z * f := ⟨z, Nat.mul_comm z f⟩
      have d4 : f ∣ 2 * e * f := ⟨2 * e, by ring⟩
      have h5 : 2 * e * f - z * f = x * e := by omega
      have h6 := Nat.dvd_sub d4 d2
      rwa [h5] at h6
    exact (Nat.Coprime.dvd_of_dvd_mul_right hcof) hd
  obtain ⟨k, hk⟩ := hdx
  have hx2f : x ≤ 2 * f := by nlinarith
  have hk2 : k ≤ 2 := by nlinarith
  interval_cases k
  · left
    have hx0 : x = 0 := by omega
    subst hx0
    constructor
    · rfl
    · constructor
      · exact hy
      · have hb : (2 : ℕ) * e * f = (2 * e) * f := by ring
        have hz : z * f = (2 * e) * f := by omega
        have := Nat.eq_of_mul_eq_mul_right (show 0 < f by omega) hz
        omega
  · right; left
    constructor
    · omega
    · constructor
      · exact hy
      · have hxe : x * e = e * f := by
          rw [hk]; ring
        have hb : (2 : ℕ) * e * f = e * f + e * f := by ring
        have hz : z * f = e * f := by omega
        have := Nat.eq_of_mul_eq_mul_right (show 0 < f by omega) hz
        omega
  · right; right
    constructor
    · omega
    · constructor
      · exact hy
      · have hxe : x * e = 2 * e * f := by
          rw [hk]; ring
        have hz : z * f = 0 := by omega
        rcases Nat.mul_eq_zero.mp hz with h0 | h0
        · omega
        · omega


/-- **The thick base dichotomy.** The γ-trap (every side of a base-β target carries at least one
`c`-edge, general in `(e,f)`) gives `z ≥ 1`, which deletes the third column of
`base_trichotomy`. Only two base decompositions survive at a separated thick member:
`(0,e,2e)` and the walls form `(f,e,e)`. -/
theorem base_dichotomy_thick {e f x y z : ℕ} (he : 1 ≤ e) (hef : e < f)
    (hco : Nat.Coprime e f) (hsep : 2 * e * f + e * e < f * f) (hz : 1 ≤ z)
    (h : x * (e * f) + y * (f * f - e * e) + z * (f * f) = e * (3 * (f * f) - e * e)) :
    (x = 0 ∧ y = e ∧ z = 2 * e) ∨ (x = f ∧ y = e ∧ z = e) := by
  rcases base_trichotomy he hef hco hsep h with h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1
  · exfalso; omega


/-! ## The thick `c`-corner chain

Writing `γ = 2α + β`, a wedge of angle `Xα + Yβ` filled by tile corners `(x,y,z)` (counts of
`α, β, γ`) satisfies `x + 2z = X` and `y + z = Y`. The three fills the chain needs are unique. -/

/-- The fill of `β` is a single `β`-corner. -/
theorem fill_beta (x y z : ℕ) (h1 : x + 2 * z = 0) (h2 : y + z = 1) :
    x = 0 ∧ y = 1 ∧ z = 0 := by omega

/-- The fill of `α` is a single `α`-corner. -/
theorem fill_alpha (x y z : ℕ) (h1 : x + 2 * z = 1) (h2 : y + z = 0) :
    x = 1 ∧ y = 0 ∧ z = 0 := by omega

/-- The fill of `α + β` is `{α, β}`. -/
theorem fill_alpha_beta (x y z : ℕ) (h1 : x + 2 * z = 1) (h2 : y + z = 1) :
    x = 1 ∧ y = 1 ∧ z = 0 := by omega

/-- **The base is never a union of `c`-edges.** `f² ∣ e(3f²−e²)` forces `f² ∣ e³`, hence `f = 1`
by coprimality. The `c`-corner chain forces every base edge to be a `c`, so it always reaches a
contradiction. -/
theorem base_not_all_c {e f : ℕ} (hf : 2 ≤ f) (he : e < f) (hco : Nat.Coprime e f)
    (h : (f * f) ∣ e * (3 * (f * f) - e * e)) : False := by
  have hfe : Nat.Coprime f e := Nat.coprime_comm.mp hco
  have hle : e * e ≤ 3 * (f * f) := by nlinarith
  have hcube : (f * f) ∣ e * (e * e) := by
    have h3 : (f * f) ∣ e * (3 * (f * f)) := ⟨e * 3, by ring⟩
    have h4 : e * (3 * (f * f)) - e * (3 * (f * f) - e * e) = e * (e * e) := by
      have hx : e * (3 * (f * f) - e * e) + e * (e * e) = e * (3 * (f * f)) := by
        rw [← Nat.mul_add]; congr 1; omega
      omega
    have h5 := Nat.dvd_sub h3 h
    rwa [h4] at h5
  have hc1 : Nat.Coprime (f * f) e := Nat.Coprime.mul_left hfe hfe
  have hcop3 : Nat.Coprime (f * f) (e * (e * e)) :=
    Nat.Coprime.mul_right hc1 (Nat.Coprime.mul_right hc1 hc1)
  have hone : f * f = 1 := Nat.eq_one_of_dvd_coprimes hcop3 dvd_rfl hcube
  have : 4 ≤ f * f := by nlinarith
  omega


/-- **The corner-parallelogram filter.** A `b`-edge cannot occupy either of the first two or
either of the last two positions of the base word, so a word of length at least four has at least
four non-`b` edges: `x + z ≥ 4`. Base columns with `x + z ≤ 3` and at least four edges are
therefore excluded. -/
theorem cornerpara_filter {x y z : ℕ} (hlen : 4 ≤ x + y + z) (hxz : x + z ≤ 3)
    (hcorner : 4 ≤ x + z) : False := by omega

end Erdos634.CChord
